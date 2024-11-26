'''
This script contains the verification stage of Alchemy. (8 CPU)
'''

import os
import re
import argparse
import subprocess  
import numpy as np
from tqdm import tqdm
from _utils import load_jsonl, save_jsonl

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--data_path", type=str)
    parser.add_argument("--output_path", type=str)
    parser.add_argument("--num_shard", type=int, default=1)
    parser.add_argument("--shard_id", type=int, default=0)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--end", type=int, default=1)
    args = parser.parse_args()
    return args

# Function to run a command line command and retrieve the output  
def run_command(command): 
    try:  
        # Run the command and capture the output  
        result = subprocess.run(command, 
                                stdout=subprocess.PIPE, 
                                stderr=subprocess.PIPE, 
                                text=True, shell=True)
                                # timeout=timeout)  
        # Check if the command was successful  
        if result.returncode != 0:  
            print("build error")
            return result.stderr
        else:
            return 0
    except subprocess.TimeoutExpired:
        print('timeout')
        return -1
    except Exception as e:  
        print("An error occurred:", e)  
        return None  

def lake_build(repo_path):
    os.chdir(repo_path)
    command = "lake build"
    result = run_command(command)
    return result

# drop the unwanted intervals and generate the new file
def generate_text(original_file, intervals, all_intervals):
    lines = original_file.split('\n')
    valid_line_nbs = []
    variants_line_nbs = []
    for interval in all_intervals:
        start, end = interval
        if interval in intervals:
            valid_line_nbs.extend(range(start-1, end))
        variants_line_nbs.extend(range(start-1, end))
    original_line_nbs = np.setdiff1d(np.arange(len(lines)), np.array(variants_line_nbs))
    output_line_nbs = np.concatenate([original_line_nbs, np.array(valid_line_nbs)]).astype(int)
    output_line_nbs.sort()
    output_file = "\n".join([lines[idx] for idx in output_line_nbs])
    output_file = re.sub(r'\n\s*\n', '\n\n', output_file)
    return output_file

if __name__ == "__main__":
    args = parse_args()
    # load the synthesized corpus
    DATA_PATH = args.data_path
    mathlib_package_path = "./mathlib4"
    output_path = args.output_path

    PACKAGE_NAME = "Mathlib"
    LIBRARY_ROOT_FILE = os.path.join(mathlib_package_path, PACKAGE_NAME + '.lean')
    corpus_path = DATA_PATH + "/synthesized_corpus.jsonl"

    if not os.path.exists(output_path):
        os.makedirs(output_path)

    files = list(load_jsonl(corpus_path))
    if args.end != -1:
        files = files[args.start:args.end]
    else:
        files = files[args.start:]
    print(f"There are {len(files)} files in total.")
    shard_size = len(files)//args.num_shard
    if args.shard_id == args.num_shard - 1:
        data = files[args.shard_id*shard_size:]
    else:
        data = files[args.shard_id*shard_size:(args.shard_id+1)*shard_size]
    print(f"SHARD_SIZE is {shard_size}")
    print(f"Current shard is {args.shard_id}")

    res = []
    for idx, file in enumerate(tqdm(data, total=len(data))):
        file_name = file['file_name']
        file_path = os.path.join(mathlib_package_path, file_name)
        # extract the old content of this file
        with open(file_path, "r") as f:
            old_str = f.read()
        # replace the ola content with new content
        with open(file_path, "w") as f:
            f.write(file['text'])
        # change the build target to current file
        with open(LIBRARY_ROOT_FILE, 'w') as f:
            module_name = file_name.replace('/', '.').replace('.lean', '')
            f.write(f"import {module_name}")
        # intialize the result
        tmp = dict()
        tmp['file_name'] = file_name
        tmp['original_text'] = old_str
        tmp['text'] = file['text']
        tmp['loc'] = file['loc']
        tmp['valid_loc'] = []
    
        if file['loc'] != ['No variants']: # if there exists variants in this file
            ## lake build the new mathlib project
            wd = os.getcwd()
            result = lake_build(mathlib_package_path)
            os.chdir(wd)
            print(f"lake build the rewrited file {file_name}")
            ## parse the output
            if result == None:
                tmp['valid_loc'] = ["subprocess error"]
            elif result == 0:
                tmp['valid_loc'] = tmp['loc']
                print('successful build')
            elif result == -1:
                tmp['valid_loc'] = ["build timeout error"]
            else:
                # find the error locations(line numbers)
                pattern = fr"({file_name}):(\d+):(\d+): error:"
                errors = re.findall(pattern, result)
                if len(errors) == 0:
                    tmp['valid_loc'] = ['parse error']
                else:
                    error_line_nbs = []
                    for error in errors:
                        _, line_nb, _ = error
                        error_line_nbs.append(int(line_nb))
                    error_line_nbs = sorted(set(error_line_nbs))
                    error_line_nbs = np.array(error_line_nbs)

                    # get the locations of all variants
                    intervals = []
                    for t, locs in file['loc'].items():
                        intervals.extend(locs)
                    intervals = np.array(intervals)
                    if len(intervals) != 0:
                        # Create a boolean array of the same shape as error_line_nbs, 
                        # with True at positions where the corresponding element of error_line_nbs is in any interval
                        in_interval = (intervals[:, 0, np.newaxis] <= error_line_nbs) & (error_line_nbs <= intervals[:, 1, np.newaxis])
                        valid_intervals = intervals[in_interval.sum(axis=1)==0]
                        with open(file_path, "w") as f:
                            f.write(generate_text(file['text'], valid_intervals, intervals))
                
                        ## rebuilt the project if trigger error break
                        wd = os.getcwd()
                        result = lake_build(mathlib_package_path)
                        os.chdir(wd)
                        print(f"lake rebuild the rewrited file {file_name}")

                        if result != 0:
                            print("rebuild exception")
                            tmp['valid_loc'] = ['rebuild error']
                        else:
                            tmp['valid_loc'] = valid_intervals.tolist()
                    else:
                        pass
        else:
            tmp['valid_loc'] = ['No variants']

        # write back the original content
        with open(file_path, "w") as f:
            f.write(old_str)
        res.append(tmp) 
    
    save_jsonl(res, os.path.join(output_path, f"verified_results_{args.shard_id}_start_{args.start}_{args.end}.jsonl"))