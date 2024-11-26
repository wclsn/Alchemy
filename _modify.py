import re
import random
from lean_dojo import interaction
from _parse import extract_id_decl_proof, parse_hypothesis, get_conclusion, parse_all_contents, get_theorem_name

def is_same(old_statement, new_statement):
    tmp = ""
    # 1. " " -> ""
    if old_statement.replace(" ", "") == new_statement.replace(" ", ""):
        return True
    
    # 2. "↑" -> "" and " " -> ""
    tmp = new_statement.replace("↑", "")
    if tmp.replace(" ", "") == old_statement.replace(" ", ""):
        return True

    # 3. "↑(xxx)" -> "xxx" (non-nested) and "↑" -> "" and " " -> ""
    if re.search(r"↑\((.*?)\)", new_statement, flags=re.DOTALL):
        tmp = re.sub(r"↑\((.*?)\)", r"\1" , new_statement)
        if "↑" in tmp:
            tmp = tmp.replace("↑", "")
        if tmp.replace(" ", "") == old_statement.replace(" ", ""):
            return True

    # 4. "↑(xxx)" -> "xxx" (nested) and "↑" -> "" and " " -> "
    contents = parse_all_contents(new_statement)
    if contents != []:
        tmp = new_statement
        for content in contents:
            escaped_content = re.escape(content)
            tmp = re.sub(f"↑\\({escaped_content}\\)", content , tmp)
        
        if "↑" in tmp:
            tmp = tmp.replace("↑", "")
        if tmp.replace(" ", "") == old_statement.replace(" ", ""):
            return True
    
    # 5. "↑(xxx)" -> "xxx" (nested) and "↑" -> "" and " " -> " and  "()" -> ""
    if tmp.replace(" ", "").replace("(", "").replace(")", "") ==\
        old_statement.replace(" ", "").replace("(", "").replace(")", ""):
            return True
    return False

'''
retrieve the identation from the beginning of the old proof
ident the inserted codeblock based on the identation level
'''
def indent_code(delimiter, old_proof, codeblock, indent_level=1):
    # extract the first proof line
    splits = old_proof.split(delimiter)
    # probably single line proof
    if not splits[1].startswith('\n'):
        indent_str = "  "
        code_block = indent_str * indent_level + codeblock.lstrip(' ') 
        return code_block 
    else:
        lines = splits[1].split('\n')
        for line in lines:
            # find the first line logic
            if line not in  ['', '\n', ' ']: 
                first_line = line
                break
        indent_str = re.search(r"^\s*", first_line).group()
        code_block = codeblock.split('\n')
        for i, line in enumerate(code_block):
            code_block[i] = indent_str * indent_level + line
        return '\n'.join(code_block)

# check whether exists naming conflicts when write new hypo
# case_name: the hypo name in invocable theorems
# hypo_names: the hypo names in target theorem
# implicit_hypo_names : the implicit hypo names in target theorems
# hypo_old: the hypo which will be replaced
def has_naming_conflicts(case_name, hypo_names, implicit_hypo_names, hypo_old):
    hypo_name_old = re.search(r"(.*?)\s+:", hypo_old).group(1)
    # conflicting with other explicit variables
    forbidden_values = []
    flag = False
    for hypo_name in hypo_names:
        for h in hypo_name:
            forbidden_values.append(h)
            if h != hypo_name_old and h == case_name:
                flag = True, 
    
    # conflicting with implicit variables
    for i_h_name in implicit_hypo_names:
        for h in i_h_name:
            forbidden_values.append(h)
            if h == case_name:
                flag = True
    
    return flag, forbidden_values

# rename the variable according mathlib naming conventions
def rename_variable(old_name, forbidden_values):
    h_list = ["h", "h₁", "h₂", "h₃", "h₄", "h₅", "h₆", "h₇", "h₈", "h₉", "h'"]
    universe_list = ["u", "v", "w"]
    type_list = ["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ", "ν"]
    prop_list = ["a", "b", "c", "d", "e", "g", "m", "n", "r", "s", "t", "v", "w", "x", "y", "z"]
    list_or_set = ["s", "t", "l", "s₁", "s₂", "s₃", "t₁", "t₂", "t₃", "l₁", "l₂", "l₃"]
    nums = ["m", "n", "k", "N", "i", "j", "k"]
    predicates = ["p", "q", "r", "p_", "q_", "r_"]
    random.shuffle(h_list)
    random.shuffle(universe_list)
    random.shuffle(type_list)
    random.shuffle(prop_list)
    random.shuffle(list_or_set)
    random.shuffle(nums)
    random.shuffle(predicates)

    if old_name[0] == "h":
        for hypo_name in h_list:
            if hypo_name != old_name and hypo_name not in forbidden_values:
                return hypo_name
    
    if old_name in prop_list:
        for prop in prop_list:
            if prop != old_name and prop not in forbidden_values:
                return prop
    
    if old_name in predicates:
        for pred in predicates:
            if pred != old_name and pred not in forbidden_values:
                return pred
    if old_name in universe_list:
        for u in universe_list:
            if u != old_name and u not in forbidden_values:
                return u
    if old_name in universe_list:
        for u in universe_list:
            if u != old_name and u not in forbidden_values:
                return u
    if old_name in type_list:
        for t in type_list:
            if t != old_name and t not in forbidden_values:
                return t
    if old_name in list_or_set:
        for l in list_or_set:
            if l != old_name and l not in forbidden_values:
                return l
    if old_name in nums:
        for num in nums:
            if num != old_name and num not in forbidden_values:
                return num
    
    return "tmp"

# simply change the name of synthesized statement into "example" 
def rename_theorem(target_theorem, statement:str, mode="example"):
    theorem_name = get_theorem_name(target_theorem, with_keyword=True)
    if mode == "example":
        new_statement = statement.replace(theorem_name, "example")
    
    # if there exists modifiers
    if re.search(r"@\[(.*?)\]", new_statement):
        new_statement = re.sub(r"@\[(.*?)\]", "", new_statement)
    new_statement = new_statement.lstrip()
    return new_statement

def reverse_rw(invocable_inst):
    inst = invocable_inst["rule"]
    templates = [
        {r"rw \[←(.*?)\]": "rw [{}]"},
        {r"rw \[←(.*?)\] at (.*)": "rw [{}] at {}"},
        {r"rw \[(.*?)\]": "rw [←{}]"},
        {r"rw \[(.*?)\] at (.*)": "rw [←{}] at {}"},
    ]
    for template in templates:
        orig, rev = list(template.items())[0]
        match = re.search(orig, inst)
        if match != None:
            if len(match.groups()) == 1:
                inv = rev.format(match.group(1))
            elif len(match.groups()) == 1:
                inv = rev.format(match.group(1), match.group(2))
            rev_inst = re.sub(orig, inv, inst)
            break
    return rev_inst

def proof_generation_rw(invocable_inst, flag, proof_str, 
                          hypo_name=None, conc_or_hypo_old=None, 
                          is_tactic_style=False, conc_forall=False):
    inst = invocable_inst["rule"]
    rev_inst = reverse_rw(invocable_inst)
    # find the delimiter for proof str
    if is_tactic_style:
        delimiter = ""
        for tmp in [":= by", ":= by\n", ":=\n  by", ":=\n      by", ":=\nby", ":=\n by"]:
            splits = proof_str.split(tmp)
            if splits[0] == '':
                delimiter = tmp
                break
        if delimiter == "":
            return None
    else:
        delimiter = ":="
        splits = proof_str.split(delimiter)
        assert splits[0] == ''

    splits = proof_str.split(delimiter)
    if len(splits) == 2:
        proof_seqs = splits[1]
    elif len(splits) > 2:
        proof_seqs = delimiter.join(splits[1:])
    if flag == "hypo":
        have_template = "have {subgoal} := by {proof_seqs}"
        have_inst = have_template.format(subgoal=conc_or_hypo_old, proof_seqs=rev_inst) 
        have_inst += f';exact {hypo_name}'
        end_inst = proof_seqs
        # if single line proof, then the original proof should also be indented
        if not splits[1].startswith('\n'):
            end_inst = indent_code(delimiter, proof_str, end_inst, indent_level=1)
    elif flag == "conclusion":
        have_template = "have : {subgoal} {delimiter} {proof_seqs}"
        have_inst = have_template.format(subgoal=conc_or_hypo_old, 
                                         delimiter=delimiter,
                                         proof_seqs=proof_seqs)
        head = "by " if not is_tactic_style else ""
        if conc_forall:
            # if it has implicit params, then we need to import it first
            _suffix = " at this;intros;exact this"
            # if it do not have implicit params, then we need to 
            # _suffix = " at this;exact this"
        else:
            _suffix = " at this;exact this"
        end_inst = head + inst + _suffix
        end_inst = indent_code(delimiter, proof_str, end_inst, indent_level=1)
    
    # do indentation
    have_inst = indent_code(delimiter, proof_str, have_inst, indent_level=1)

    # concat the different parts of proof
    prefix = splits[0] + delimiter + '\n'
    suffix = end_inst if end_inst.startswith('\n') else '\n' + end_inst
    new_proof = prefix + have_inst + suffix
    return new_proof


def modify_theorem_rw(target_theorem, invocable_inst):
    
    res = extract_id_decl_proof(target_theorem, raw_string=True)
    nodes, strs = res[:3], res[3:]
    inst = invocable_inst["rule"]  
    next_state = invocable_inst["next_state"]

    if re.search(r"rw \[(.*?)\] at (.*)", inst):
        flag = "hypo" 
        hypo_name = re.search(r"rw \[(.*?)\] at (.*)", inst).group(2)
    else:
        flag = "conclusion"
    
    # tactic style or term style
    is_tactic_style = True if target_theorem.has_tactic_proof() else False

    # change the statement
    statement_node = nodes[1]
    if flag == "conclusion":
        # parse AST -> old conc str -> replace
        _, conc_old = get_conclusion(statement_node)  
        conc_new = next_state.split('\n')[-1].lstrip('⊢')
        start_idx = 0
        statement_str = strs[1]
        while True:
            find_idx = statement_str.find(conc_old, start_idx)
            if find_idx == -1:
                break
            else:
                start_idx = find_idx + 1
        statement_str = statement_str[:start_idx-1] + statement_str[start_idx-1:].replace(conc_old, conc_new)
        if conc_new.lstrip(' ').startswith("∀") and re.search(r"\{.*?\}", conc_new):
            conc_forall = True
        else:
            conc_forall = False

    elif flag == "hypo":
        # parse AST -> old hypo str -> replace
        hypo_names, _, hypo_strs = parse_hypothesis(statement_node)
        for i, hypo in enumerate(hypo_names):
            if hypo_name in hypo:
                hypo_str_old = hypo_strs[i]
                break
        assumptions_new = interaction.parse_goals.parse_goals(next_state)[0].assumptions # type: ignore
        for assump in assumptions_new:
            if assump.ident == hypo_name:
                hypo_new_type = assump.lean_type
                break
        statement_str = strs[1].replace(hypo_str_old, f"{hypo_name} : {hypo_new_type}")  #hypo_old  (name: type)
    else:
        raise Exception
    
    # check if is the same
    if is_same(strs[1], statement_str):
        return None
    # drop invalid identifiers or notations
    invalid_notions = [".num", "some", "byteIdx", "down", "Nonempty", "toLex", "toDual", "ofLex"]
    for notion in invalid_notions:
        if notion in statement_str:
            return None
    # refine the statement
    statement_str = statement_str.replace("‖", "|")
    statement_str = rename_theorem(target_theorem, statement_str, mode="example")
    # change the proof
    args = (invocable_inst, flag)
    kwargs = {"proof_str": strs[2], "is_tactic_style": is_tactic_style}
    if flag == "hypo":
        kwargs['hypo_name'] = hypo_name
        kwargs['conc_or_hypo_old'] = hypo_str_old
    elif flag == 'conclusion':
        kwargs['conc_or_hypo_old'] = conc_old
        kwargs['conc_forall'] = conc_forall
    new_proof = proof_generation_rw(*args, **kwargs)  # drop the invalid delimiter
    if new_proof == None:
        return None
    # merge the statement and proof
    new_theorem = statement_str + new_proof  
    return new_theorem

def proof_generation_apply(cases_goals, inst, proof_str, is_tactic_style):
    if len(cases_goals) == 1:
        conjecture = inst + "; assumption"
    elif len(cases_goals) > 1:
        conjecture = inst + "<;> assumption"
    else:
        raise Exception("no available case and corresponding goal")
    
    if is_tactic_style:
        delimiter = ""
        for tmp in [":= by", ":= by\n", ":=\n  by", ":=\n      by", ":=\nby", ":=\n by"]:
            splits = proof_str.split(tmp)
            if splits[0] == '':
                delimiter = tmp
                break
        if delimiter == "":
            return None
    else:
        delimiter = ":="
        splits = proof_str.split(delimiter)
        assert splits[0] == ''

    splits = proof_str.split(delimiter)
    if len(splits) == 2:
        proof_seqs = splits[1]
    elif len(splits) > 2:
        proof_seqs = delimiter.join(splits[1:])
    conjeture = indent_code(delimiter, proof_str, conjecture)
    prefix = splits[0] + delimiter + '\n'
    suffix = proof_seqs if proof_seqs.startswith('\n') else '\n' + proof_seqs
    new_proof = prefix + conjeture + suffix
    return new_proof

def modify_theorem_apply(target_theorem, invocable_inst, debug=False):
    res = extract_id_decl_proof(target_theorem, raw_string=True)
    nodes, strs = res[:3], res[3:]
    hypo_names, _, _, implicit_hypo_names = parse_hypothesis(nodes[1], return_implicit=True)
    proof_str = strs[2]
    inst = invocable_inst["rule"]
    next_state = invocable_inst["next_state"]
    next_state = next_state.replace("unsolved goals\n", "")
    # tactic style or term style
    is_tactic_style = True if target_theorem.has_tactic_proof() else False
    # check metavariables
    flag = "metav" if "?" in next_state else "subgoal"

    # split dojo states to get subgoals
    sub_states = next_state.split('\n\n')
    # assume each subgoal has a name "case"
    cases_goals = dict()
    for sub_state in sub_states:
        case = re.search(r"case (.*?)\n", sub_state).group(1)
        goal = re.search(r"⊢ (.*)", sub_state).group(1)
        if not cases_goals.get(case):
            cases_goals[case] = [goal]
        else:
            cases_goals[case].append(goal)
    
    # check metaV for each case
    metaVs = []
    for case in list(cases_goals.keys()):
        if re.search(f"\\?{case}", next_state):
            metaVs.append(case)
    
    if debug:
        print(f"next_state:\n {next_state}")
        print(f"metaVs:\n {metaVs}")
        print(f"cases_goals:\n {cases_goals}")
    
    # change the statement
    '''
    1. find the changed hypo and its location
    2. if exists metavariables, get all subgoals, find the holes first and then fill the holes
    if not, just get new subgoals
    3. append the new hypo to the statement get new statement
    '''
    matches = re.search(r"have (.*) := by apply (.*)", inst)
    hypo_str, _ = matches.group(1), matches.group(2)
    statement_old = strs[1]
    # get the new hyposA
    hypo_template = "({hypo_name} : {hypo_type})"
    hypo_new = []
    if flag == "metav":
        # for each metav, find the corresponding case
        rename_metaV = metaVs.copy()
        for i, metaV in enumerate(metaVs):
            for goal in cases_goals[metaV]:
                if f"?" not in goal:  
                    break
            flag_, forbidden_names = has_naming_conflicts(metaV, hypo_names, implicit_hypo_names, hypo_str)
            if flag_:
                case = rename_variable(metaV, forbidden_values=forbidden_names)
                rename_metaV[i] = case
            else:
                case = metaV
            hypo_new.append(hypo_template.format(hypo_name=case, hypo_type=goal))
        
        for case, goals in list(cases_goals.items()):
            if case not in metaVs:
                for idx, metaV in enumerate(metaVs):
                    goals = [goal.replace(f'?{metaV}', rename_metaV[idx]) for goal in goals]
                
                flag_, forbidden_names = has_naming_conflicts(case, hypo_names, implicit_hypo_names, hypo_str)
                if flag_:
                    case = rename_variable(case, forbidden_values=forbidden_names)
                elif case in rename_metaV:
                    case = rename_variable(case, forbidden_values=forbidden_names + rename_metaV)
                else:
                    pass
                for goal in goals:
                    hypo_new.append(hypo_template.format(hypo_name=case, hypo_type=goal))
            else:
                if len(goals) > 1:
                    flag_, forbidden_names = has_naming_conflicts(case, hypo_names, implicit_hypo_names, hypo_str)
                    case = rename_variable(case, forbidden_values=forbidden_names + rename_metaV)
                    for goal in goals:
                        if "?" in goal:
                            for idx, metaV in enumerate(metaVs):
                                goal = goal.replace(f'?{metaV}', rename_metaV[idx])
                            hypo_new.append(hypo_template.format(hypo_name=case, hypo_type=goal))

    elif flag == "subgoal":
        for case, goals in list(cases_goals.items()):
            flag, forbidden_names = has_naming_conflicts(case, hypo_names, implicit_hypo_names, hypo_str)
            if flag:
                case = rename_variable(case, forbidden_values=forbidden_names)
            else:
                pass
            for goal in goals:
                hypo_new.append(hypo_template.format(hypo_name=case, hypo_type=goal))
    hypo_new = ' '.join(hypo_new)
    
    statement_new = statement_old.replace('(' + hypo_str + ')', hypo_new)
    statement_new = rename_theorem(target_theorem, statement_new, mode="example")

    # change the proof
    # just insert the lemma directly
    proof_new = proof_generation_apply(cases_goals, inst, proof_str, is_tactic_style)
    if proof_new == None:
        return None
    new_theorem = statement_new + proof_new
    return new_theorem