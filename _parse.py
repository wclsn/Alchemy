from lean_dojo import data_extraction
from lean_dojo.data_extraction.ast import *

# extract the id, decl and proof node for each theorem 
def extract_id_decl_proof(traced_theorem, raw_string=False):
    id = dict()
    decl = dict()
    proof = dict()
    proof_node_classes = (CommandDeclvalsimpleNode, CommandDeclvaleqnsNode, CommandWherestructinstNode)

    def extract_decl_proof_callback(node, _):
        if isinstance(node, CommandDeclidNode):  # theorem_name_node
            id["start"], id["end"], id["node"] = node.start, node.end, node
        elif isinstance(node, CommandDeclsigNode): # theorem_statement_node
            decl["end"], decl["node"] =  node.end, node
        elif isinstance(node, proof_node_classes):  # maybe should use termbytactic node
            proof["start"], proof["end"], proof["node"] = node.start, node.end, node
        else:
            pass

    ast = traced_theorem.ast
    decl["start"] = ast.start
    ast.traverse_preorder(extract_decl_proof_callback, node_cls=None)
    # get the id
    id_node = id["node"]
    # get the proof
    proof_node = proof["node"]
    # get the decl
    decl_node = decl["node"]
    if not raw_string:
        return id_node, decl_node, proof_node
    else:
        theorem_name = id_node.lean_file[id["start"]:id["end"]]
        statement_str = decl_node.lean_file[decl["start"]:decl["end"]]
        proof_str = proof_node.lean_file[proof["start"]:proof["end"]]
        return id_node, decl_node, proof_node, theorem_name, statement_str, proof_str

# parse ast and get the hypothesis name
# if the hypothesis name is "_" just ignore it
def parse_hypothesis(statement_node, return_implicit=False):  
    # This list will hold the first IdentNode4 (the hypothesis name) for each TermExplicitbinderNode4  
    hypo_nodes = []
    hypo_names = []
    hypo_strs = []
    implicit_hypo_names = []
      
    # This flag indicates whether we are currently within a TermExplicitbinderNode4  
    within_explicit_binder = False  
    within_implicit_binder = False  
    '''Callback for finding TermExplicitbinderNode4 nodes
    logic: 
    1. give the statement node(CommandDeclsigNode)
    2. get its first child, which is a NullNode
    3. find the outermost term explicit binder node
    4. we can get the hypothesis name by using the children of the TermExplicitbinderNode
     <AtmoNode> <NullNode> <NullNode> <NullNode> <AtomNode> 
        - find its first NullNode child
            - get the IdentNode from this child
            - filtering the hypothesis name (e.g. remove "_")
            - if the hypothesis looks like (a b c : Type), it will get [["a", "b", "c"]]
        - find its second NullNode child -> hypo type
        - locate the str between the start of first NullNode and the end of the second NullNode
    '''
    def get_explicit_param_callback(node, _):  
        nonlocal within_explicit_binder  
        if isinstance(node, TermExplicitbinderNode):  
            if within_explicit_binder:  
                # Skip this node because we're already within a TermExplicitbinderNode4  
                return True  
            within_explicit_binder = True  
            hypo_nodes.append(node)
            childrens = node.children
            hypo_name_node = childrens[1]            
            hypo_names.append([c.raw_val for c in hypo_name_node.children if isinstance(c, IdentNode) and c.raw_val != "_"])
            hypo_type_node = childrens[2]
            hypo_str = statement_node.lean_file[hypo_name_node.start:hypo_type_node.end]
            hypo_strs.append(hypo_str)  # e.g. (h: α)

            within_explicit_binder = False  
            # Return True to indicate that children of this node should not be visited  
            return True  
        return False  # Continue traversal for other nodes  
    
    '''
    callback for finding implicit variable
    logic:
    1. give the statement node(CommandDeclsigNode)
    2. get its first child, which is a NullNode
    3. find the outermost OtherNodes whose kind is Lean.Parser.Term.implicitBinder
    4. check the valid OtherNode's children(AtomNode, NullNode, NullNode, AtomNode) -> to be checked
        - find its first NullNode child
            - get the IdentNode from this child -> implicit hypo name
    '''
    def get_implicit_param_callback(node, _):
        nonlocal within_implicit_binder  
        if isinstance(node, OtherNode) and node.kind == "Lean.Parser.Term.implicitBinder":  
            if within_implicit_binder:  
                # Skip this node because we're already within a TermExplicitbinderNode4  
                return True  
            within_implicit_binder = True  
            childrens = node.children
            hypo_name_node = childrens[1]            
            implicit_hypo_names.append([c.raw_val for c in hypo_name_node.children if isinstance(c, IdentNode) and c.raw_val != "_"])

            within_implicit_binder = False  
            # Return True to indicate that children of this node should not be visited  
            return True  
        return False  # Continue traversal for other nodes  

      
    # Traverse the statement node with the specific callback  
    hypo = statement_node.children[0]
    assert isinstance(hypo, NullNode)
    hypo.traverse_preorder(get_explicit_param_callback, node_cls=None)  
    if return_implicit:
        hypo.traverse_preorder(get_implicit_param_callback, node_cls=None)
        return hypo_names, hypo_nodes, hypo_strs, implicit_hypo_names

    return hypo_names, hypo_nodes, hypo_strs

# judge a theorem whether can be used to simplify the target theorem
def isTheoremApplicableForSimplification(traced_theorem):
    flag = False
    ast = traced_theorem.ast
    line_nb = ast.start.line_nb
    column_nb = ast.start.column_nb
    modifier_pos = data_extraction.lean.Pos.from_str(f"({line_nb-1}, {1})")

    whole_theorem = ast.lean_file[modifier_pos:ast.end]

    if "@[simp]" in whole_theorem:
        # print(whole_theorem)
        flag = True
    return flag

def get_conclusion(statement_node):
    conclusion = dict()
    '''
    1. find TermTypespecNode of the statement node
    2. get the children of this node : [AtomNode, OtherNode | TermByTacticNode | IdentNode]
    3. get conclusion from the second child
    '''
    def get_conclusion_callback(node, _):
        if isinstance(node, TermTypespecNode):
            children = node.children
            conclusion["start"], conclusion["end"], conclusion["node"] = children[1].start, children[1].end, children[1]
            
    statement_node.traverse_preorder(get_conclusion_callback, node_cls=None)
    return conclusion["node"], statement_node.lean_file[conclusion["start"]:conclusion["end"]]

# return the theorem name
# with_keyword: e.g. "theorem" or "lemma"
# if with_keyword,return will be "theorem xxx" or "lemma xxx
def get_theorem_name(target_theorem, with_keyword=True):
    theorem_node = target_theorem.ast
    children = theorem_node.children
    if isinstance(children[0], AtomNode):
        keyword_start = children[0].start
        id_start = children[1].start
        id_end = children[1].end
    elif isinstance(children[0], CommandDeclmodifiersNode):
        group_node = children[1]
        keyword_start = group_node.children[0].start
        id_start = group_node.children[1].start
        id_end = group_node.children[1].end
    
    if with_keyword:
        return target_theorem.ast.lean_file[keyword_start:id_end]
    else:
        return target_theorem.ast.lean_file[id_start:id_end]

# parse all the results inside "↑()"
def parse_all_contents(expression):  
    parsed_contents = []  # List to store all parsed contents  
    start_index = 0  # Starting index for the search  
  
    while True:  
        # Find the index of the ↑ symbol starting from start_index  
        arrow_index = expression.find('↑', start_index)  
        if arrow_index == -1:  
            break  # If no more ↑ symbols are found, exit the loop  
  
        # Initialize counters  
        open_paren_index = -1  
        close_paren_index = -1  
        open_parentheses_count = 0  
  
        # Start searching for parentheses after the ↑ symbol  
        for i in range(arrow_index, len(expression)):  
            char = expression[i]  
            if char == '(':  
                open_parentheses_count += 1  
                if open_parentheses_count == 1:  
                    open_paren_index = i  
            elif char == ')':  
                open_parentheses_count -= 1  
                if open_parentheses_count == 0:  
                    close_paren_index = i  
                    break  # We found the matching closing parenthesis  
  
        # If we found matching parentheses, extract the content  
        if open_paren_index != -1 and close_paren_index != -1:  
            content = expression[open_paren_index + 1:close_paren_index]  
            parsed_contents.append(content)  
            start_index = close_paren_index + 1  # Update start_index to search for the next ↑ symbol  
        else:  
            # If no matching parentheses are found after the current ↑ symbol,  
            # skip to the next character and continue searching  
            start_index = arrow_index + 1  
  
    return parsed_contents  
  