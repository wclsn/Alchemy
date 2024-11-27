import tqdm
from _parse import extract_id_decl_proof, parse_hypothesis
from _utils import save_jsonl
from lean_dojo import LeanError, TacticState
from lean_dojo.interaction.dojo import DojoHardTimeoutError

"""
for each theorem's hypothesis and conclusion
test whether the invoked theorem can be used to mutate it
"""
def get_apply_insts(p_theorem_name, hypo_strs):

    inst_template = "have {hypo} := by apply {theorem_name}"
    apply_insts = []
    if len(hypo_strs) != 0:
        for hypo_str in hypo_strs:
            apply_insts.append(
                inst_template.format(hypo=hypo_str, theorem_name=p_theorem_name)
            )
    return apply_insts

def get_rw_insts(p_theorem_name, hypo_names):
    rw_insts = [
        "rw [{theorem_name}]".format(theorem_name=p_theorem_name),  
        "rw [←{theorem_name}]".format(theorem_name=p_theorem_name),
    ]
    if len(hypo_names) != 0:
        for hypo_name in hypo_names:
            for hypo in hypo_name:
                rw_insts.append(
                    "rw [{theorem_name}] at {h}".format(
                        theorem_name=p_theorem_name, h=hypo
                    ))
                rw_insts.append(
                    "rw [←{theorem_name}] at {h}".format(
                        theorem_name=p_theorem_name, h=hypo
                    ))
    return rw_insts

# hypos
def is_invocable_theorem(
    dojo, init_state, possible_invocable_theorem, hypos, mode="rw"
):
    p_t_name = possible_invocable_theorem.theorem.full_name
    # decouple the hypos
    hypo_names, _, hypo_strs = hypos
    # get the lean insts
    if mode == "rw":
        insts = get_rw_insts(p_t_name, hypo_names)
    elif mode == "apply":
        insts = get_apply_insts(p_t_name, hypo_strs)
    else:
        raise ValueError("The mode should be either 'rw' or 'apply'")

    flag = False
    res = []
    errors = []

    for _, inst in enumerate(insts):
        try:
            next_state = dojo.run_tac(init_state, inst)
        except DojoHardTimeoutError:
            raise 
        except Exception as e:
            print(f"Error in running the dojo tac {inst}")
        else:
            if isinstance(next_state, LeanError):
                if mode == "apply" and "unsolved goals" in next_state.error:
                    flag = True
                    res.append(
                        {
                            "init_state": init_state.pp,
                            "next_state": next_state.error,
                            "rule": inst,
                        }
                    )
                else:
                    errors.append(
                        {
                            "init_state": init_state.pp,
                            "next_state": next_state.error,
                            "rule": inst,
                        }
                    )
            elif isinstance(next_state, TacticState):
                flag = True
                res.append(
                    {
                        "init_state": init_state.pp,
                        "next_state": next_state.pp,
                        "rule": inst,
                    }
                )

    return flag, hypo_names, res, errors


def get_invocable_theorems_with_dojo(
    target_theorem,
    dojo,
    state_0,
    possible_invocable_theorems,
    with_checkpoint=False,
    output_path=None,
    checkpoint_interval=1000,
    with_tqdm=True,
    cache_error_file=False,
    mode="rw",
):
    # parse the ast of the target theorem
    nodes = extract_id_decl_proof(target_theorem)
    hypothesis_names = parse_hypothesis(nodes[1])
    invocable_theorems = []
    results = []
    error_list = []

    if with_tqdm:
        iterator = tqdm.tqdm(
            possible_invocable_theorems,
            desc="Checking invocable theorems",
            total=len(possible_invocable_theorems),
        )
    else:
        iterator = possible_invocable_theorems

    for idx, possible_invocable_theorem in enumerate(iterator):
        do = True
        if possible_invocable_theorem != target_theorem:
            if isinstance(possible_invocable_theorem.theorem.full_name, str):
                # drop the theorems which will make dojo crash (This is a temporary solution which depends on the mathlib commit)
                if "$" in possible_invocable_theorem.theorem.full_name:
                    print(possible_invocable_theorem.theorem.full_name)
                    do = False
                else:
                    do = True
            else:  # there exists some theorems whose name is None
                do = False

            if do:
                flag, hypo_names, res, errors = is_invocable_theorem(
                    dojo,
                    state_0,
                    possible_invocable_theorem,
                    hypos=hypothesis_names,
                    mode=mode,
                )
                if flag:
                    invocable_theorems.append(possible_invocable_theorem)
                    results.append(
                        {
                            possible_invocable_theorem.theorem.full_name: res,
                            "hypo_name": hypo_names,
                        }
                    )
                else:
                    error_list.append(
                        {
                            possible_invocable_theorem.theorem.full_name: errors,
                            "hypo_name": hypo_names,
                        }
                    )

        # incrementally save the results
        if with_checkpoint:
            if idx % checkpoint_interval == 0:
                save_jsonl(
                    results,
                    output_path + f"/{target_theorem.theorem.full_name}.jsonl",
                    mode_="a",
                    show_message=False,
                )
                if cache_error_file: 
                    save_jsonl(
                        error_list,
                        output_path
                        + f"/{target_theorem.theorem.full_name}_errors.jsonl",
                        mode_="a",
                        show_message=False,
                    )
                with open(output_path + "/local_checkpoint.txt", "w") as f:
                    f.write(str(idx))
                # clear the results and errors
                results = []
                errors = []

            # if finished this loop, reset the checkpoint to 0
            if idx == len(possible_invocable_theorems) - 1:
                with open(output_path + "/local_checkpoint.txt", "w") as f:
                    f.write(str(0))

    return invocable_theorems, results, error_list

def filtering_single_goal(invocable_theorems):
    res = []
    for t in invocable_theorems:
        insts = list(t.items())[0][1]
        filtered_insts = []
        for inst in insts:
            if len(inst["next_state"].split("\n\n")) > 1:
                pass
            else:
                filtered_insts.append(inst)

        if len(filtered_insts) > 0:
            res.append(
                {list(t.keys())[0]: filtered_insts, "hypo_name": list(t.values())[1]}
            )
    return res
