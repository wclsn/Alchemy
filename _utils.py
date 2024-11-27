import os
import json
import argparse
import numpy as np
from pathlib import Path
from typing import Iterable, Union, Any
from lean_dojo import DojoInitError
from lean_dojo.data_extraction.traced_data import TracedTheorem, TracedFile

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--file_path', type=str, default=None)
    parser.add_argument('--split', type=int, default=1)
    args = parser.parse_args()
    return args

def load_jsonl(file: Union[str, Path]) -> Iterable[Any]:
    with open(file, "r", encoding="utf-8") as f:
        for line in f:
            try:
                yield json.loads(line)
            except:
                print("Error in loading:", line)

def save_jsonl(samples, save_path, mode_="w", show_message=False):
    # ensure path
    folder = os.path.dirname(save_path)
    os.makedirs(folder, exist_ok=True)

    with open(save_path, mode=mode_, encoding="utf-8") as f:
        for sample in samples:
            f.write(json.dumps(sample) + "\n")
    if show_message:
        print("Saved to", save_path)

def random_select(total_num, select_num):
    return np.random.choice(total_num, select_num, replace=False)

# write a specific lean theorem to its original lean file: only useful when it is used for test
# this function is modified from 
# https://github.com/lean-dojo/LeanDojo/blob/405513a55181bb0552e41833c13862f3a03c9139/src/lean_dojo/interaction/dojo.py
def write_back(file_path, target_theorem: TracedTheorem, traced_file: TracedFile, additional_imports=[], modified_theorems=[]) -> str:
    if target_theorem is None:
        raise DojoInitError(
            f"Failed to locate the theorem"
        )
    # locate the target theorem
    theorem_start, theorem_end = target_theorem.start, target_theorem.end
    lean_file = traced_file.lean_file

    # get additional imports
    if len(additional_imports) > 0:
        code_import = "\n".join(f"import {_}" for _ in additional_imports) + "\n\n"
    else:
        code_import = ""
    
    # get original theorems
    code_theorem = lean_file[theorem_start:theorem_end]
    
    # get modified theorems
    if len(modified_theorems) > 0:
        code_modified_theorems = "\n\n".join(modified_theorems) + "\n"
    else:
        code_modified_theorems = ""
    
    code_before_theorem = lean_file[lean_file.start_pos():theorem_start]

    code_after_theorem = lean_file[theorem_end:lean_file.end_pos()]
    if "align" in code_after_theorem.split('\n')[0]:
        code_after_theorem = code_after_theorem[1:]
        aligner = code_after_theorem.split('\n')[0]
    else:
        aligner = ''
    prefix = code_import + code_before_theorem + code_theorem + '\n' + aligner + '\n\n' 
    modified_code = prefix + code_modified_theorems + code_after_theorem

    # locate the modified theorems
    modified_theorems_start = len(prefix.split('\n'))
    modified_theorems_end = modified_theorems_start + len(code_modified_theorems.split('\n'))
    print(f"The start pos of the modified theorems is line {modified_theorems_start}")
    print(f"The end pos of the modified theorems is line {modified_theorems_end}")

    with open(file_path + target_theorem.theorem.full_name + '.lean', "w") as f:
        f.write(modified_code)
    return modified_code

if __name__ == "__main__":
    pass
