import argparse
from lean_dojo import LeanGitRepo, trace

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=str, default="https://github.com/leanprover-community/mathlib4")
    parser.add_argument("--commit", type=str, default="3c307701fa7e9acbdc0680d7f3b9c9fed9081740")
    args = parser.parse_args()
    return args

if __name__ == '__main__':
    args = parse_args()
    repo = LeanGitRepo(
        args.repo,
        args.commit
    )

    traced_repo = trace(repo)