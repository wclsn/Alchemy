'''
This script is used to find the invocable theorems for the target theorems.(8 Core)
'''
import os
import pickle
import logging
import argparse
from logging import FileHandler
from lean_dojo import LeanGitRepo, Dojo, Theorem
from lean_dojo.interaction.dojo import DojoHardTimeoutError
from lean_dojo.data_extraction.ast import CommandDeclvalsimpleNode
from _utils import save_jsonl, random_select
from _logic import get_invocable_theorems_with_dojo
from _parse import extract_id_decl_proof, parse_hypothesis

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--personal_token', type=str, default='') # github personal access token
    parser.add_argument('--mode', type=str, default="generate")  # generate, random_test or ordered_test
    parser.add_argument('--test_num', type=int, default=10) # be used in test mode
    parser.add_argument('--start', type=int, default=0) # the start of possible_invocable_theorems
    parser.add_argument('--end', type=int, default=-1)
    parser.add_argument('--target_start', type=int, default=0) # the start of target theorems
    parser.add_argument('--target_end', type=int, default=-1)
    # the checkpoint is used to resume when exception occurs
    parser.add_argument('--with_checkpoint', action='store_true')
    parser.add_argument('--checkpoint_interval', type=int, default=1000)
    parser.add_argument('--cache_error_file', action="store_true")

    parser.add_argument('--gen_mode', type=str, default="rw") # rw or apply
    parser.add_argument("--hard_timeout", type=int, default=3600) # the hard timeout for each theorem(default is 1 hour)

    parser.add_argument('--output_path', type=str, default="outputs")
    parser.add_argument('--data_path', type=str, default="data")
    args = parser.parse_args()
    return args

def init_logger(i, output_path):
    logger = logging.getLogger()
    log_path = output_path + '/logs'
    if not os.path.exists(log_path):
        os.makedirs(log_path)
    log_name = log_path + f'/test_proc_{i}.log'
    logger.setLevel(logging.INFO)
    handler = FileHandler(log_name, mode='w', encoding='utf-8')
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    if logger.hasHandlers():  
        logger.handlers.clear() 
    logger.addHandler(handler)
    logger.propagate = False
    return logger

def get_start_offset(output_path):
    start_offset = 0
    partial_completed = False
    for file in os.listdir(output_path):
        if file.endswith(".jsonl") and "errors" not in file:
            start_offset += 1
        if "local_checkpoint" in file:
            with open(output_path + '/' + file, 'r') as f:
                remain_num = int(f.read())
                if remain_num != 0:
                    partial_completed = True
    if partial_completed:
        start_offset -= 1
    return start_offset

def write_checkpoint(checkpoint_file, remain_num):
    with open(checkpoint_file, 'w') as f:
        f.write(str(remain_num))

def main():
    args = parse_args()
    OUTPUT_DIR = args.output_path
    DATA_DIR = args.data_path
    logger = init_logger(0, OUTPUT_DIR)
    # set output path and data path
    output_path = OUTPUT_DIR + f'/outputs_{args.target_start}_{args.target_end}'
    if not os.path.exists(output_path):
        os.makedirs(output_path, exist_ok=True)

    checkpoint_file = output_path + "/checkpoint.txt"  
    local_checkpoint_file = output_path + "/local_checkpoint.txt" 
    # set github personal access token to avoid rate limit error
    if args.personal_token != '':
        os.environ['GITHUB_ACCESS_TOKEN'] = args.personal_token
    
    # initialize the repo and load the cached traced repo
    # here we only load the traced theorems to reduce the memory usage
    # You can get the candidate theorems by trace the dojo and pickle the traced theorems
    args.traced_repo_path = DATA_DIR + '/candidate_theorems.pickle'
    repo = LeanGitRepo(
        "https://github.com/leanprover-community/mathlib4",
        "3c307701fa7e9acbdc0680d7f3b9c9fed9081740"
    )

    # get possible invocable theorems and target theorems
    possible_invocable_theorems = pickle.load(open(args.traced_repo_path, 'rb'))
    offset = get_start_offset(output_path)
    target_theorems = []
    for idx, theorem in enumerate(possible_invocable_theorems):
        try:
            nodes = extract_id_decl_proof(theorem)
        except:
            pass
        else:
            if isinstance(nodes[2], CommandDeclvalsimpleNode) and "Mathlib" in theorem.theorem.file_path.as_posix():
                if args.gen_mode == "rw":
                    target_theorems.append(theorem)
                elif args.gen_mode == "apply":
                    statement_node = nodes[1]
                    hypos = parse_hypothesis(statement_node)
                    if len(hypos[0]) > 0:
                        target_theorems.append(theorem)
                else:
                    raise ValueError("Invalid gen_mode")

    # get the target theorems (check the existing checkpoints)
    if args.target_end == -1:
        pass
    else:
        assert args.target_end >= args.target_start + offset
        if args.with_checkpoint:
            target_theorems = target_theorems[args.target_start+offset:args.target_end]
        else:
            target_theorems = target_theorems[args.target_start:args.target_end]

    # get test_theorems
    # the test mode is only useful when debug
    test_theorems = []
    if args.mode == "random_test":
        idxs = random_select(len(target_theorems), args.test_num)
        for idx in idxs:
            test_theorems.append(target_theorems[idx])
    elif args.mode == "ordered_test":
        test_theorems = target_theorems[0:args.test_num]
    elif args.mode == "generate":
        test_theorems = target_theorems
    else:
        raise ValueError("Invalid mode")

    if args.end == -1:
        if not args.with_checkpoint:
            pass
        else:
            possible_invocable_theorems = possible_invocable_theorems[args.start:]
    else:
        possible_invocable_theorems = possible_invocable_theorems[args.start:args.end]
    print(f'There are {len(test_theorems)} test theorems')
    print(f'There are {len(possible_invocable_theorems)} possible invocable theorems')

    total_count = len(test_theorems)
    for target_theorem in test_theorems:
        # the Dojo will change current work dir to a tmp dir
        host_wd = os.getcwd() # e.g. /home/xxx/lean4
        logger.info(f"Start to test the theorem {target_theorem.theorem.full_name}")

        results = []
        errors = []
        try:
            theorem = Theorem(repo, target_theorem.theorem.file_path.as_posix(), target_theorem.theorem.full_name)
            dojo, init_state = Dojo(theorem, hard_timeout=args.hard_timeout).__enter__()
        except Exception as e:
            print(f"Error in initializing the dojo for the theorem {target_theorem.theorem.full_name}")
            logger.error("Init Error" + e)
        else:
            print(f"Dojo has been initialized for the theorem {target_theorem.theorem.full_name}")
            with_tqdm = True 
            try:
                invocable_theorems = get_invocable_theorems_with_dojo(
                                        target_theorem, 
                                        dojo,
                                        init_state,
                                        possible_invocable_theorems,
                                        with_checkpoint=args.with_checkpoint,
                                        output_path=output_path,
                                        checkpoint_interval=args.checkpoint_interval,
                                        with_tqdm=with_tqdm,
                                        cache_error_file=args.cache_error_file,
                                        mode=args.gen_mode)
            except DojoHardTimeoutError:
                logger.error(f"Hard Timeout for the theorem {target_theorem.theorem.full_name}")
                # if timeout occurs, we need to change the local checkpoint to 0(so that the checkpoint will not be used)
                with open(local_checkpoint_file, "w") as f:
                    f.write(str(0))
            else:
                if not args.with_checkpoint:
                    results, errors = invocable_theorems[1], invocable_theorems[2]
                    save_jsonl(results, output_path + f"/{target_theorem.theorem.full_name}.jsonl")
                    if args.cache_error_file:
                        save_jsonl(errors, output_path + f"/{target_theorem.theorem.full_name}_errors.jsonl")
            finally:
                os.chdir(host_wd)
                total_count -= 1
                write_checkpoint(checkpoint_file, total_count)
        finally:
            dojo.__exit__(None, None, None)

if __name__ == "__main__":
    main()