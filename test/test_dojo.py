from pathlib import Path
from lean_dojo import Theorem, Dojo, LeanGitRepo

if __name__ == "__main__":

    repo = LeanGitRepo(
        "https://github.com/leanprover-community/mathlib4",
        "3c307701fa7e9acbdc0680d7f3b9c9fed9081740"
    ) 

    try:
        theorem = Theorem(repo, Path("Mathlib/Algebra/Algebra/Basic.lean"), "algebraMap.coe_zero")
        dojo, state_0 = Dojo(theorem).__enter__()
    except Exception as e:
        print("Error: ", e)
    else:
        dojo.__exit__(None, None, None)