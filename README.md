# Alchemy-Code
This repository stores the code for Paper [Alchemy: Amplifying Theorem-Proving Capability through Symbolic Mutation](https://arxiv.org/abs/2410.15748)

## Setup
### Prerequisites
- Python 3.10
### Environment Configuration
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
pip install lean-dojo==1.7.1
pip install numpy tqdm
# Set the env variables 
export PATH=$$HOME/.elan/bin:$$PATH  
export GITHUB_ACCESS_TOKEN="Your Github Access Token"
elan toolchain install leanprover/lean4:v4.6.0-rc1
```
## Tutorial
We present an tutorial (pipeline.ipynb) for how to mutating a demo theorem using theorems in Mathlib. It includes the process to synthesize its variants, verify their correctness using Lean and trace the state-tactics.

## Alchemy
We provide several scripts for data-synthesis on mathlib.
### Find Invocable Theorems
```bash
# On each CPU node
# target_start;target_end : the start and end idx of target theorems on this node
# gen_mode : (rw|apply)
# timeout : hard timeout for each dojo env to reduce the time cost, usually 1h(3600s)
bash ./scripts/run_with_checkpoint.sh {target_start} {target_end} {gen_mode} {timeout}
```
### Mutate the Theorems
```bash
# You can reference the implementation in mutate.py.
python mutate.py
```
### Verify the Theorems
```bash
# On each CPU node, we verify a subset of modified Lean files.
# start, end : the start idx and end idx of modified lean files
# num_of_shard : how many shards are splitted between the start and end
# shard_id : the id for current node
python verify.py --data_path {synthesized_data_path} --output_path {output_path} --num_shard {num_of_shard} --shard_id {shard_id} --start {start} --end {end}
```
### Trace the Tactics
```bash
# You should write the variants into the mathlib repo and create a new github repo.
# Then you can use Leandojo to trace this repo.
# The traced cache is stored in traced_cache.
python extract_state_tactic.py --num_procs {num_procs} --repo_url {repo_url} --repo_commit {repo_commit} --traced_cache {the path of traced cache} --synthesized_corpus_path {synthesized corpus}
```