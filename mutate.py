import os
import sys
sys.path.append("..")
import tqdm
import random
random.seed(42)
os.environ["GITHUB_ACCESS_TOKEN"] = "Your Github Token"
from lean_dojo import LeanGitRepo,trace
from lean_dojo.data_extraction.ast import *
from _utils import load_jsonl, save_jsonl
from _logic import filtering_single_goal
from _modify import modify_theorem_rw, modify_theorem_apply

GEN_MODE = "apply" # "rw" or "apply"
INVOCABLE_THEOREMS_DIR = ""  # The directory which stores invocable theorems for different target theorems.

if __name__ == "__main__":
    repo = LeanGitRepo(
        "https://github.com/leanprover-community/mathlib4",
        "3c307701fa7e9acbdc0680d7f3b9c9fed9081740"
    )
    traced_repo = trace(repo)
    target_theorems = traced_repo.get_traced_theorems()
    name2theorem = {target_theorem.theorem.full_name:target_theorem for target_theorem in target_theorems} 
    files = os.listdir(INVOCABLE_THEOREMS_DIR)
    non_empty_files = []
    for file in tqdm.tqdm(files):
        insts = list(load_jsonl(os.path.join(INVOCABLE_THEOREMS_DIR, file)))
        if len(insts) > 0:
            non_empty_files.append(file)
    print(f"There are {len(non_empty_files)} non-empty files")

    theorem2output = {}
    file2theorem = {}
    for target_theorem in target_theorems:
        try:
            idx = files.index(target_theorem.theorem.full_name + ".jsonl")
        except:
            continue
        else:
            # if exists output file
            theorem2output[target_theorem] = files[idx]
            traced_file_path = target_theorem.theorem.file_path.as_posix()
            if not file2theorem.get(traced_file_path, 0):
                file2theorem[traced_file_path] = [target_theorem]
            else:
                file2theorem[traced_file_path].append(target_theorem)

    # for each traced_file find the related target theorems and the start and end of these theorems
    # for each target_theorem in this file, modify the theorem and get variants
    # insert all modified theorems of all target theorems in this file at once (record their location)
    lean_corpus = []
    test_files = list(file2theorem.items())
    for traced_file, target_theorems in tqdm.tqdm(test_files, total=len(test_files)):
        modifier_blackboard = {}
        for target_theorem in target_theorems:
            # locate this theorem
            theorem_ast = target_theorem.ast
            leanfile = theorem_ast.lean_file
            start, end = theorem_ast.start, theorem_ast.end
            # get the output_file
            output_file = theorem2output[target_theorem]
            # for this target theorem get its modified version
            try:
                invocable_theorems = list(load_jsonl(output_file))
            except:
                print(f"Error in loading the file {output_file}")
            else:
                if GEN_MODE == "rw":
                    filtered_invocable_theorems = filtering_single_goal(invocable_theorems)
                elif GEN_MODE == "apply":
                    filtered_invocable_theorems = invocable_theorems
                new_theorems = []
                for idx, invocable_theorem in enumerate(filtered_invocable_theorems):
                    insts = list(invocable_theorem.values())[0]
                    for inst in insts:
                        if GEN_MODE == "rw":
                            new_theorem = modify_theorem_rw(target_theorem, inst)
                        elif GEN_MODE == "apply":
                            try:
                                new_theorem = modify_theorem_apply(target_theorem, inst)
                            except:
                                new_theorem = None
                        if new_theorem:
                            new_theorems.append(new_theorem)

            if not modifier_blackboard.get(target_theorem, 0) and len(new_theorems) > 0:
                modifier_blackboard[target_theorem] = {"start":start, "end": end, "new_theorems": new_theorems}

        # replace this file all at once
        res = dict()
        res['file_name'] = traced_file
        res['loc'] = dict() # e.g. {theorem_name: [(start, end), (start, end)]}
        offset = 0
        old_file = '\n'.join(leanfile.code)
        
        if len(modifier_blackboard.keys()) != 0:
            for target_theorem, modifier in modifier_blackboard.items():
                name = target_theorem.theorem.full_name
                res['loc'][name] = []
                start, end, new_theorems = modifier["start"], modifier["end"], modifier["new_theorems"]
                original_theorem = leanfile[start:end]
                start = start.line_nb + offset
                end = end.line_nb + offset 
                original_end = end
                # get the location of each modified theorems
                for idx, new_theorem in enumerate(new_theorems):
                    if idx == 0:
                        theorem_start = end + 3
                    else:
                        theorem_start = end + 2
                    theorem_end = theorem_start + len(new_theorem.split('\n')) - 1
                    end = theorem_end
                    res['loc'][name].append((theorem_start, theorem_end))
                offset += theorem_end - original_end
                new_theorem = original_theorem +"\n" + "\n\n" + "\n\n".join(new_theorems)
                new_file = old_file.replace(original_theorem, new_theorem)
                old_file = new_file
            res['text'] = new_file
        else:
            res['text'] = old_file
            res['loc'] = ['No variants']
        lean_corpus.append(res)

    print(f"The file number of lean_corpus is {len(lean_corpus)}")
    save_jsonl(lean_corpus, f"synthesized_corpus_{GEN_MODE}_without_verify.jsonl")