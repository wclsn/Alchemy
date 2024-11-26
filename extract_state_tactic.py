import os
import argparse
import multiprocessing
from tqdm import tqdm
from lean_dojo import LeanGitRepo
from lean_dojo.data_extraction.ast import *
from lean_dojo.data_extraction.lean import Pos
from _utils import load_jsonl, save_jsonl
from lean_dojo.data_extraction.traced_data import TracedRepo, TracedFile, TracedTactic

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num_procs", type=int, default=24)
    parser.add_argument("--repo_url", type=str)
    parser.add_argument("--repo_commit", type=str)
    parser.add_argument("--traced_cache", type=str)
    parser.add_argument("--synthesized_corpus_path", type=str)
    args = parser.parse_args()
    return args

# extract the id, decl and proof node for each theorem 
def find_example_node(file_node: FileNode):
    examples = []
    def extract_decl_proof_callback(node, _):
        if isinstance(node, CommandExampleNode):
            examples.append(node)
    file_node.traverse_preorder(extract_decl_proof_callback, node_cls=None)
    return examples

# the code below is largely modified from the lean_dojo library
def extract_state_tactics(example_node: CommandExampleNode, atomic_only: bool = False):
    """Return a list of traced tactics in the proof."""
    tacs = get_traced_tactics_lean4(example_node, atomic_only)
    # Deduplicate.
    signatures = set()
    tacs_dedup = []
    for sig in tacs:
        if sig not in signatures:
            signatures.add(sig)
            tacs_dedup.append(sig)
    return tacs_dedup

def get_traced_tactics_lean4(
    example_node: CommandExampleNode,
    atomic_only: bool = False
) -> List[TracedTactic]:
    tacs = []

    def _callback(node, _):
        if type(node) not in (
            TacticTacticseq1IndentedNode,
            TacticTacticseqbracketedNode,
        ):
            return
        for tac_node in node.get_tactic_nodes(atomic_only):
            if (
                hasattr(tac_node, "state_before")
                and tac_node.state_before is not None
            ):
                # Tactics outside theorem/lemma definitions are not recorded.
                tacs.append((tac_node.state_before, tac_node.tactic, tac_node.state_after))

    example_node.traverse_preorder(_callback, node_cls=None)
    return tacs

def worker(i, data, repo_path, prefix, show_tqdm=False, commit='', results_dir=""):
    print(f"worker {i} has been started with {len(data)} examples")
    res = []
    json_res = []
    if show_tqdm:
        iterator= tqdm(enumerate(data), total=len(data))
    else:
        iterator = enumerate(data)
    for idx, item in iterator:
        file_path = item['file_name']
        xml_path = file_path.replace(".lean", ".trace.xml")
        if os.path.exists(os.path.join(repo_path, prefix, xml_path)):
            traced_file = TracedFile.from_xml(repo_path, os.path.join(repo_path, prefix, xml_path), repo)
            ast = traced_file.ast  # find the file-level ast
            examples = find_example_node(ast)
            for example in examples:
                tmp = dict()
                theorem = example.lean_file[example.start:example.end]
                tactics = extract_state_tactics(example)
                res.extend(tactics)
                tmp["theorem"] = theorem
                tmp['tactics'] = tactics
                tmp["file_name"] = file_path
                json_res.append(tmp)

    if not os.path.exists(results_dir):
        os.makedirs(results_dir)
    json_path = f"{results_dir}/state_tactics_{i}_{commit}.jsonl"
    save_jsonl(json_res, json_path)
    print(f"Worker {i} has been finished.")
    print(f"Worker {i} has saved {len(res)} tactics.")
    return 0

if __name__ == "__main__":
    args = parse_args()
    lean_corpus = list(load_jsonl(args.synthesized_corpus_path))
    repo_url = args.repo_url
    repo_commit = args.repo_commit
    repo = LeanGitRepo(repo_url, repo_commit)
    prefix = ".lake/build/ir"
    # repo_path = "/home/v-shaonanwu/.cache/lean_dojo/wclsn-robot_ml_rl_nlp_homework-a9d29fe5412e4a4b83a40c1fb1ae3535033f2cbe/robot_ml_rl_nlp_homework"
    traced_cache_path = args.traced_cache

    # Create a list to hold the processes
    print("start multiprocessing")
    processes = []
    shard_size = len(lean_corpus) // args.num_procs
    for i in range(args.num_procs):
        start = i * shard_size
        end = (i + 1) * shard_size
        if i == args.num_procs - 1:
            end = len(lean_corpus)
        chunk = lean_corpus[start:end]
        show_tqdm = i == 0
        p = multiprocessing.Process(
            target=worker, 
            args=(
                  i,
                  chunk,
                  traced_cache_path, 
                  prefix, 
                  show_tqdm,
                  repo_commit)
                )
        p.start()
        processes.append(p)

    # Wait for all processes to finish
    for p in processes:
        p.join()
    