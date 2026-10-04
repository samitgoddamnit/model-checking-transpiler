#!/usr/bin/env python3
"""
c_to_prog.py

Translates a C source file into the .prog format 
"""

import argparse
from pathlib import Path
from typing import Optional, Literal

import clang.cindex as cx


from model_checker import TRACKED_ACTIONS, DEFAULT_CONSTRAINTS



# -- CFG ---------------------

class CFGNode:
    """Node in simplified control flow graph."""
    def __init__(self, node_id: int, kind: str):
        self.id = node_id
        self.kind = kind
        self.successors: list[int] = []
        self.predecessors: list[int] = []
        self.statements: list = []


class CFGBuilder:
    def __init__(self):
        self.nodes: dict[int, CFGNode] = {}
        self.node_counter = 0
        self.entry_node = None
        self.exit_node = None

    def new_node(self, kind: str) -> int:
        node_id = self.node_counter
        self.node_counter += 1
        self.nodes[node_id] = CFGNode(node_id, kind)
        return node_id

    def build_from_function(self, func_cursor: cx.Cursor) -> tuple[int, int]:
        """Build CFG; returns (entry_id, exit_id)."""
        self.entry_node = self.new_node("entry")
        self.exit_node = self.new_node("exit")

        body = next(
            (c for c in func_cursor.get_children()
             if c.kind == cx.CursorKind.COMPOUND_STMT),
            None,
        )

        if body is None:
            self.nodes[self.entry_node].successors.append(self.exit_node)
            self.nodes[self.exit_node].predecessors.append(self.entry_node)
            return self.entry_node, self.exit_node

        current = self.entry_node
        for stmt in body.get_children():
            current = self._process_stmt(stmt, current)

        self.nodes[current].successors.append(self.exit_node)
        self.nodes[self.exit_node].predecessors.append(current)
        return self.entry_node, self.exit_node

    def _process_stmt(self, stmt: cx.Cursor, pred: int) -> int:
        if stmt.kind == cx.CursorKind.IF_STMT:
            return self._process_if(stmt, pred)
        elif stmt.kind == cx.CursorKind.WHILE_STMT:
            return self._process_while(stmt, pred)
        elif stmt.kind == cx.CursorKind.FOR_STMT:
            return self._process_for(stmt, pred)
        else:
            self.nodes[pred].statements.append(stmt)
            return pred

    def _process_if(self, if_stmt: cx.Cursor, pred: int) -> int:
        cond_node = self.new_node("if_cond")
        then_node = self.new_node("if_then")
        else_node = self.new_node("if_else")
        join_node = self.new_node("if_join")

        self.nodes[pred].successors.append(cond_node)
        self.nodes[cond_node].predecessors.append(pred)

        self.nodes[cond_node].successors.extend([then_node, else_node])
        self.nodes[then_node].predecessors.append(cond_node)
        self.nodes[else_node].predecessors.append(cond_node)

        children = list(if_stmt.get_children())
        then_stmt = children[1] if len(children) > 1 else None
        else_stmt = children[2] if len(children) > 2 else None

        then_end = self._add_stmts_to_block(then_stmt, then_node) if then_stmt else then_node
        else_end = self._add_stmts_to_block(else_stmt, else_node) if else_stmt else else_node

        self.nodes[then_end].successors.append(join_node)
        self.nodes[else_end].successors.append(join_node)
        self.nodes[join_node].predecessors.extend([then_end, else_end])

        return join_node

    def _process_while(self, while_stmt: cx.Cursor, pred: int) -> int:
        cond_node = self.new_node("while_cond")
        body_node = self.new_node("while_body")
        exit_node = self.new_node("while_exit")

        self.nodes[pred].successors.append(cond_node)
        self.nodes[cond_node].predecessors.append(pred)

        self.nodes[cond_node].successors.extend([body_node, exit_node])
        self.nodes[body_node].predecessors.append(cond_node)
        self.nodes[exit_node].predecessors.append(cond_node)

        children = list(while_stmt.get_children())
        body_stmt = children[1] if len(children) > 1 else None
        body_end = self._add_stmts_to_block(body_stmt, body_node) if body_stmt else body_node

        self.nodes[body_end].successors.append(cond_node)
        self.nodes[cond_node].predecessors.append(body_end)

        return exit_node

    def _process_for(self, for_stmt: cx.Cursor, pred: int) -> int:
        cond_node = self.new_node("for_cond")
        body_node = self.new_node("for_body")
        exit_node = self.new_node("for_exit")

        self.nodes[pred].successors.append(cond_node)
        self.nodes[cond_node].predecessors.append(pred)

        self.nodes[cond_node].successors.extend([body_node, exit_node])
        self.nodes[body_node].predecessors.append(cond_node)
        self.nodes[exit_node].predecessors.append(cond_node)

        children = list(for_stmt.get_children())
        init_stmt = children[0] if len(children) > 0 else None
        body_stmt = children[3] if len(children) > 3 else (children[2] if len(children) > 2 and children[2].kind == cx.CursorKind.COMPOUND_STMT else None)
        inc_stmt = children[2] if len(children) > 2 else None

        if init_stmt is not None:
            if init_stmt.kind == cx.CursorKind.COMPOUND_STMT:
                for c in init_stmt.get_children():
                    self.nodes[pred].statements.append(c)
            else:
                self.nodes[pred].statements.append(init_stmt)


        body_end = self._add_stmts_to_block(body_stmt, body_node) if body_stmt else body_node
        if inc_stmt is not None:

            self.nodes[body_end].statements.append(inc_stmt)


        self.nodes[body_end].successors.append(cond_node)
        self.nodes[cond_node].predecessors.append(body_end)

        return exit_node

    def _add_stmts_to_block(self, stmt: cx.Cursor, block: int) -> int:
        if stmt.kind == cx.CursorKind.COMPOUND_STMT:
            current = block
            for child in stmt.get_children():
                if child.kind in (cx.CursorKind.IF_STMT, cx.CursorKind.WHILE_STMT, cx.CursorKind.FOR_STMT):
                    current = self._process_stmt(child, current)
                else:
                    self.nodes[current].statements.append(child)
            return current
        else:
            self.nodes[block].statements.append(stmt)
            return block


class ReversalAnalyser:
    """Analyze reversal counts per execution path through CFG.
    
    Tracks the sequence of operations (inc/dec) for each variable on each path,
    enabling accurate counting of reversals (transitions between inc and dec).
    """
    def __init__(self, cfg: CFGBuilder, translator):
        self.cfg = cfg
        self.translator = translator

    def analyse(self) -> dict[str, list[dict]]:
        """Return: var_key -> [{'sequence': [...], 'reversals': int}, ...] per path.
        """
        visited_paths = []
        self._dfs_paths(self.cfg.entry_node, {}, visited_paths)

        result: dict[str, list[dict]] = {}
        for path_state in visited_paths:
            for var_key, state in path_state.items():
                if var_key not in result:
                    result[var_key] = []
                
                operations = state.get('operations', [])
                reversals = self._count_reversals(operations)
                
                result[var_key].append({
                    'sequence': operations.copy(),
                    'reversals': reversals
                })
        
        return result
    
    def _count_reversals(self, operations: list[str]) -> int:
        if not operations:
            return 0
        
        # Variables with 'unknown' in their paths are removed from analysis for completeness
        if 'unknown' in operations:
            return -1  
        
        meaningful_ops = [op for op in operations if op in ('inc', 'dec')]
        
        if len(meaningful_ops) <= 1:
            return 0
        
        reversals = 0
        for i in range(1, len(meaningful_ops)):
            if meaningful_ops[i] != meaningful_ops[i-1]:
                reversals += 1
        
        return reversals

    def _dfs_paths(
        self,
        node_id: int,
        current_state: dict,
        all_paths: list,
        visited: Optional[set] = None,
    ) -> None:
        """DFS exploring all paths.
        """
        if visited is None:
            visited = set()

        if node_id in visited:
            # Loop back-edge: mark variables as unknown 
            finalized = {}
            for k, v in current_state.items():
                ops = v.get('operations', []).copy()
                # mark unknown if not already present so _count_reversals will exclude it
                if 'unknown' not in ops:
                    ops.append('unknown')
                finalized[k] = {
                    'operations': ops,
                    'latest': v.get('latest'),
                }
            all_paths.append(finalized)
            return

        visited.add(node_id)
        node = self.cfg.nodes[node_id]

        for stmt in node.statements:
            self._classify_statement(stmt, current_state)

        if not node.successors:
            # Terminal node: finalize path
            finalized = {}
            for k, v in current_state.items():
                finalized[k] = {
                    'operations': v.get('operations', []).copy(),
                    'latest': v.get('latest'),
                }
            all_paths.append(finalized)
        else:
            for succ_id in node.successors:
                # copy state for successor
                succ_state = {}
                for k, v in current_state.items():
                    succ_state[k] = {
                        'operations': v.get('operations', []).copy(),
                        'latest': v.get('latest'),
                    }
                visited_copy = visited.copy()
                self._dfs_paths(succ_id, succ_state, all_paths, visited_copy)

    def _classify_statement(self, stmt: cx.Cursor, current_state: dict) -> None:

        if stmt.kind == cx.CursorKind.UNARY_OPERATOR:
            update = self.translator._classify_counter_update(stmt)
            if update is not None:
                var_key, kind = update
                
                if var_key not in current_state:
                    current_state[var_key] = {'operations': [], 'latest': None}
                
                state = current_state[var_key]
                state['operations'].append(kind)
                return
        
        if stmt.kind == cx.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
            update = self.translator._classify_counter_update(stmt)
            if update is not None:
                var_key, kind = update
                
                if var_key not in current_state:
                    current_state[var_key] = {'operations': [], 'latest': None}
                
                state = current_state[var_key]
                state['operations'].append(kind)
                return
        
        if stmt.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(stmt)
            if parts is None or parts[1] != "=":
                return
            
            lhs_expr, _, rhs_expr = parts
            var = ast_extract_variable(lhs_expr)
            
            if var is None:
                return
            
            var_key = self.translator._resolve_decl_key_in_expr(stmt, var)
            
            # Initialize state if new variable
            if var_key not in current_state:
                current_state[var_key] = {'operations': [], 'latest': None}
            
            state = current_state[var_key]
            
            # x = constant
            const = ast_extract_integer(rhs_expr)
            if const is not None:
                self._update_state_with_constant(state, const, var)
                return
            
            # Case 2: x = x +/- constant or x = constant +/- x
            if rhs_expr.kind == cx.CursorKind.BINARY_OPERATOR:
                lin = self.translator._extract_linear_expr(rhs_expr)
                if lin is not None:
                    rhs_var, offset = lin
                    if rhs_var == var:
                        # x = x +/- offset
                        if offset > 0:
                            self._handle_arithmetic_update(state, "+=", offset, var)
                        elif offset < 0:
                            self._handle_arithmetic_update(state, "-=", -offset, var)
                        else:
                            state['operations'].append('neutral')
                        return
            
            # x = y. If y has a single known value in current_state, treats it as a constant assignment.
            # if y==x keep neutral. conservatively marked as unknown if none of these are true.
            rhs_var = ast_extract_variable(rhs_expr)
            if rhs_var is not None:
                if rhs_var == var:
                    state['operations'].append('neutral')
                    return

                # try to resolve declaration key for rhs and consult current_state
                rhs_key = self.translator._resolve_decl_key_in_expr(rhs_expr, rhs_var)
                rhs_state = current_state.get(rhs_key)
                if rhs_state is not None:
                    # if rhs has a single concrete value and is not unknown, treat as constant
                    if 'unknown' not in rhs_state.get('operations', []) and rhs_state.get('latest') is not None:
                        const_val = rhs_state.get('latest')
                        self._update_state_with_constant(state, const_val, var)
                        return
                state['operations'].append('unknown')
                return
            
            # Case 4: Unknown assignment
            state['operations'].append('unknown')

    def _update_state_with_constant(self, state: dict, const: int, var: str) -> None:
        prev = state.get('latest')
        if prev is not None:
            if const > prev:
                state['operations'].append('inc')
            elif const < prev:
                state['operations'].append('dec')
            else:
                state['operations'].append('neutral')
        else:
            state['operations'].append('neutral')
        state['latest'] = const

    def _handle_arithmetic_update(self, state: dict, op: str, amount: int, var: str) -> None:
        if op == "+=":
            if amount > 0:
                state['operations'].append('inc')
            elif amount < 0:
                state['operations'].append('dec')
            else:
                state['operations'].append('neutral')
            if state['latest'] is not None:
                state['latest'] += amount
        elif op == "-=":
            if amount > 0:
                state['operations'].append('dec')
            elif amount < 0:
                state['operations'].append('inc')
            else:
                state['operations'].append('neutral')
            if state['latest'] is not None:
                state['latest'] -= amount


# -- indented writer ------------------------------------------------------------

class Writer:
    def __init__(self) -> None:
        self._lines: list[str] = []
        self._depth: int = 0

    def w(self, line: str = "") -> None:
        self._lines.append("    " * self._depth + line)

    def blank(self) -> None:
        self._lines.append("")

    def indent(self) -> None:
        self._depth += 1

    def dedent(self) -> None:
        self._depth -= 1

    def get(self) -> str:
        return "\n".join(self._lines)


# -- AST extraction helpers ----

def ast_extract_integer(expr: Optional[cx.Cursor]) -> Optional[int]:
    """Extract or evaluate integer from an expression.
    
    Handles:
    - Direct integer literals: 5 → 5
    - Unary negation: -5, -(5) → -5
    - Simple constant folding: (5 + 3), (10 - 5), (2 * 3), (10 / 2) → evaluated result
    - Wrapper nodes: UNEXPOSED_EXPR
    
    Returns the integer value or None if not evaluable to a constant.
    """
    if expr is None:
        return None
    
    # Handle wrapper nodes like UNEXPOSED_EXPR
    if expr.kind == cx.CursorKind.UNEXPOSED_EXPR:
        children = list(expr.get_children())
        if len(children) == 1:
            return ast_extract_integer(children[0])
        return None
    
    # Direct integer literal
    if expr.kind == cx.CursorKind.INTEGER_LITERAL:
        tokens = list(expr.get_tokens())
        for tok in tokens:
            if tok.spelling:
                try:
                    return int(tok.spelling)
                except ValueError:
                    pass
        return None
    
    # Unary minus: -(expr) or -expr
    if expr.kind == cx.CursorKind.UNARY_OPERATOR:
        parts = ast_get_unary_operator_parts(expr)
        if parts:
            op, operand = parts
            if op == "-":
                val = ast_extract_integer(operand)
                if val is not None:
                    return -val
            elif op == "+":
                # Unary plus: just return the operand's value
                return ast_extract_integer(operand)
        return None
    
    # Binary constant folding: (5 + 3) → 8, etc.
    if expr.kind == cx.CursorKind.BINARY_OPERATOR:
        parts = ast_get_binary_operator_parts(expr)
        if parts:
            left_expr, op, right_expr = parts
            left_val = ast_extract_integer(left_expr)
            right_val = ast_extract_integer(right_expr)
            

            if left_val is not None and right_val is not None:
                try:
                    if op == "+":
                        return left_val + right_val
                    elif op == "-":
                        return left_val - right_val
                    elif op == "*":
                        return left_val * right_val
                    elif op == "/":
                        # Integer division
                        if right_val != 0:
                            return left_val // right_val
                    elif op == "%":
                        if right_val != 0:
                            return left_val % right_val
                except:
                    pass
        return None
    
    return None


def ast_extract_variable(expr: Optional[cx.Cursor]) -> Optional[str]:
    """Extract variable name from a DECL_REF_EXPR, handling wrapper nodes like UNEXPOSED_EXPR."""
    if expr is None:
        return None
    
    # Handle wrapper nodes like UNEXPOSED_EXPR
    if expr.kind == cx.CursorKind.UNEXPOSED_EXPR:
        children = list(expr.get_children())
        if len(children) == 1:
            return ast_extract_variable(children[0])
        return None
    
    if expr.kind == cx.CursorKind.DECL_REF_EXPR:
        return expr.spelling
    return None


def ast_get_binary_operator_parts(node: cx.Cursor) -> Optional[tuple[cx.Cursor, str, cx.Cursor]]:
    """Extract left operand, operator, and right operand from BINARY_OPERATOR node.
    
    Returns (left_expr, op_token, right_expr) or None if not a valid binary op.
    """
    if node.kind != cx.CursorKind.BINARY_OPERATOR:
        return None
    
    children = list(node.get_children())
    if len(children) != 2:
        return None
    
    left, right = children
    
    logical_ops = {'&&', '||'}
    known_ops = {'<<', '>>', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '=', 
                 '+', '-', '*', '/', '%', '&', '|', '^', '<=', '>=', '==', '!=', '<', '>'}
    

    toks = list(node.get_tokens())
    
    # Search for logical operators first (for compound conditions like n > 0 && x < 10)
    for tok in toks:
        if tok.spelling in logical_ops:
            return (left, tok.spelling, right)
    
    # Then search for other operators
    for tok in toks:
        if tok.spelling in known_ops:
            return (left, tok.spelling, right)
    
    return None


def ast_get_unary_operator_parts(node: cx.Cursor) -> Optional[tuple[str, cx.Cursor]]:
    """Extract operator and operand from UNARY_OPERATOR node.
    
    Returns (op_token, operand_expr) or None if not valid.
    """
    if node.kind != cx.CursorKind.UNARY_OPERATOR:
        return None
    
    children = list(node.get_children())
    if len(children) != 1:
        return None
    
    operand = children[0]
    
    known_ops = {'++', '--', '+', '-', '!', '~', '*', '&'}
    
    for tok in node.get_tokens():
        if tok.spelling in known_ops:
            return (tok.spelling, operand)
    
    return None


def ast_get_compound_assign_parts(node: cx.Cursor) -> Optional[tuple[cx.Cursor, str, cx.Cursor]]:
    """Extract var, operator, and right side from COMPOUND_ASSIGNMENT_OPERATOR node.
    
    Returns (var_expr, op_token, rhs_expr) or None.
    """
    if node.kind != cx.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
        return None
    
    children = list(node.get_children())
    if len(children) != 2:
        return None
    
    var, rhs = children
    
    known_ops = {'+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>='}
    
    # Get operator directly from AST tokens
    for tok in node.get_tokens():
        if tok.spelling in known_ops:
            return (var, tok.spelling, rhs)
    
    return None


# -- main translator ------------------------------------------------------------

class ProgGen:
    def __init__(
        self,
        tracked_actions: dict[str, dict],
        constraints: list[str] = None,
        max_reversals: int = 0,
    ) -> None:
        self.tracked_actions = tracked_actions
        self.constraints = constraints if constraints else ["malloc != free"]
        self.max_reversals = max_reversals
        self.known: set[str] = set()   # functions defined in this TU
        self.known_decls: dict[str, cx.Cursor] = {}
        self.counter_vars: dict[str, dict] = {}
        self.declname_map: dict[str, str] = {}
        self.bool_decls: dict[str, tuple[str, Optional[str]]] = {}
        # seeded variable decl keys (to bump reversal budget)
        self.seeded_vars: set[str] = set()
        # call graph: func_name -> set of (callee_name, line, col)
        self.call_graph: dict[str, set] = {}
        # recursive functions detected during call-graph analysis
        self.recursive_funcs: set[str] = set()
        # literal call-sites: (caller, callee, line, col) -> list of (arg_index, literal_value)
        self.literal_callsites: dict = {}
        # clone mapping: (callee, line, col) -> clone_name
        self.clone_map: dict = {}
        # cloned parameter keys: clone_name -> {param_index -> cloned_decl_key}
        self.clone_param_keys: dict = {}
        self.out   = Writer()

    # -- Main Entry Point --------------------------------------------------

    def generate(self, tu: cx.TranslationUnit, entry: Optional[str], output_path: Optional[str] = None, dump_ast: bool = False) -> str:
        source_file = tu.spelling   # path of the file passed to parse()
        
       
        
        # collect defined function names
        for cur in tu.cursor.get_children():
            if (cur.kind == cx.CursorKind.FUNCTION_DECL
                    and cur.is_definition()
                    and self._is_in_source(cur, source_file)):
                self.known.add(cur.spelling)
                self.known_decls[cur.spelling] = cur

        if entry is None:
            entry = "main" if "main" in self.known else None


        self._build_call_graph(tu, source_file)
        self._detect_recursive_functions()
        

        self._collect_literal_callsites(tu, source_file)

        self._collect_booleans(tu, source_file)


        self.counter_vars = self._infer_counter_vars(tu, source_file)
        
      
        self._generate_clones(tu, source_file)

        #once clones are generated, iteratively rescan for more potential cloning sites.
        #max iteration limit set to avoid state bloat 
        max_iter = 10
        for _ in range(max_iter):
            new_added = False
            existing_clones = dict(self.clone_map)

            for (orig_callee, _, _), clone_name in list(existing_clones.items()):
                for (caller, callee, line, col), args in list(self.literal_callsites.items()):
                    if caller != orig_callee:
                        continue
                    new_key = (clone_name, callee, line, col)
                    if new_key not in self.literal_callsites:
                        self.literal_callsites[new_key] = list(args)
                        new_added = True
            if not new_added:
                break
            # create clones for any newly-visible call-sites
            self._generate_clones(tu, source_file)


        self._prescan_seeds(tu, source_file)

        #if a function has no calls in the TU, removed from PCo model
        removable_originals: set[str] = set()
        for func in list(self.known):
            if func in self.recursive_funcs:
                continue
            if entry and func == entry:
                continue
            # Check whether any call-site references this function
            has_callsite = False
            for (caller, callee, line, col) in self.literal_callsites.keys():
                if callee == func:
                    has_callsite = True
                    break
            if not has_callsite:
                removable_originals.add(func)

        if removable_originals:
            for func in removable_originals:
                decl = self.known_decls.get(func)
                if decl is None:
                    continue
                # remove parameter keys
                params = [ch for ch in decl.get_children() if ch.kind == cx.CursorKind.PARM_DECL]
                for p in params:
                    key = self._cursor_key(p)
                    if key in self.counter_vars:
                        del self.counter_vars[key]
                    if key in self.declname_map:
                        del self.declname_map[key]
                    # remove any seeded variants tied to this key
                    to_rm = {sv for sv in self.seeded_vars if sv == key or sv.startswith(key + "@")}
                    self.seeded_vars -= to_rm

                # remove local var decl keys (VAR_DECL inside the body)
                body = next((c for c in decl.get_children() if c.kind == cx.CursorKind.COMPOUND_STMT), None)
                if body:
                    stack = [body]
                    while stack:
                        n = stack.pop()
                        try:
                            if getattr(n, 'kind', None) == cx.CursorKind.VAR_DECL:
                                key = self._cursor_key(n)
                                if key in self.counter_vars:
                                    del self.counter_vars[key]
                                if key in self.declname_map:
                                    del self.declname_map[key]
                                to_rm = {sv for sv in self.seeded_vars if sv == key or sv.startswith(key + "@")}
                                self.seeded_vars -= to_rm
                        except Exception:
                            pass
                        for ch in n.get_children():
                            stack.append(ch)

        # record pruned originals so emission skips them
        self._pruned_originals = removable_originals


        
        # header emission
        for vkey, vinfo in self.counter_vars.items():
            if vkey in self.declname_map:
                continue
            vname = vinfo['name']
            # sanitize to alphanum and underscore only
            safe = ''.join(c if (c.isalnum() or c == '_') else '_' for c in vname)
            self.declname_map[vkey] = safe

        # if a variable is seeded at a call site the reversal budget is increased by 1
        for vkey in sorted(self.counter_vars, key=lambda k: self.counter_vars[k]['name']):
            vinfo = self.counter_vars[vkey]
            vname = vinfo['name']
            base_rev = vinfo.get('reversals', 0)
            if vkey in self.seeded_vars:
                base_rev += 1
            safe = self.declname_map.get(vkey, vname)
            self.out.w(f"counter {safe} reversals {base_rev}")
        self.out.blank()

        # emit global boolean declarations (owner is None)
        for bkey, (bname, owner) in sorted(self.bool_decls.items(), key=lambda kv: kv[1][0]):
            if owner is not None:
                continue
            safe = self.declname_map.get(bkey)
            if safe is None:
                safe = ''.join(c if (c.isalnum() or c == '_') else '_' for c in bname)
                if safe in set(self.declname_map.values()):
                    safe = safe + '_b'
                self.declname_map[bkey] = safe
            self.out.w(f"bool {safe}")
        if entry and entry in self.known:
            self.out.w(f"start {entry}")
        self.out.blank()

        #currently not supporting threads
        self.out.w("switches 0")
        self.out.blank()

        for constraint_str in self.constraints:
            self.out.w(f"constraint ({constraint_str})")
        self.out.blank()

        # ------------------------ CODE GENERATION -------------------------- 
        
        # Translate each procedure (source file only)
        for cur in tu.cursor.get_children():
            if (cur.kind == cx.CursorKind.FUNCTION_DECL
                    and cur.is_definition()
                    and self._is_in_source(cur, source_file)):
                func_name = cur.spelling
                # Emit original procedure unless it was pruned above
                if func_name not in getattr(self, '_pruned_originals', set()):
                    self._proc(cur)
                # Emit clones for this function
                for (callee, line, col), clone_name in self.clone_map.items():
                    if callee == func_name:
                        self._proc(cur, emit_as_clone=clone_name)

        prog_output = self.out.get()
        
        if dump_ast:
            from pathlib import Path
            if output_path:
                output_dir = Path(output_path).parent
                output_dir.mkdir(parents=True, exist_ok=True)
                ast_dump_file = output_dir / f"{Path(output_path).stem}_ast.txt"
            else:
                output_dir = Path("output")
                output_dir.mkdir(exist_ok=True)
                ast_dump_file = output_dir / "ast_dump.txt"
            self._dump_ast_to_file(tu, str(ast_dump_file))
        
        return prog_output

    # -- Clone Management Helpers ------------------------------------------

    def in_cloned_proc(self) -> bool:
        """Check if currently emitting a cloned procedure."""
        return hasattr(self, '_emitting_clone') and self._emitting_clone
    
    def get_remapped_key(self, orig_key: str) -> str:
        """If emitting a clone, remap parameter keys to cloned keys."""
        if not self.in_cloned_proc() or not self.current_clone_for_param_key:
            return orig_key
        # Look for this key in the clone's parameter mapping
        param_map = self.clone_param_keys.get(self.current_clone_for_param_key, {})
        for cloned_key in param_map.values():
            if cloned_key.startswith(orig_key + "#"):
                return cloned_key
        return orig_key

    

    def _build_call_graph(self, tu: cx.TranslationUnit, source_file: str) -> None:
        """Build a call graph mapping each function to its callees (callee_name, line, col)."""
        for cur in tu.cursor.get_children():
            if not (cur.kind == cx.CursorKind.FUNCTION_DECL and cur.is_definition() and self._is_in_source(cur, source_file)):
                continue
            caller = cur.spelling
            self.call_graph[caller] = set()
            body = next((c for c in cur.get_children() if c.kind == cx.CursorKind.COMPOUND_STMT), None)
            if body is None:
                continue
            self._scan_calls_for_graph(body, caller)

    def _scan_calls_for_graph(self, node: cx.Cursor, caller: str) -> None:
        """Recursively scan for CALL_EXPR nodes and add to call graph."""
        if node.kind == cx.CursorKind.CALL_EXPR:
            callee = node.spelling
            if callee in self.known:
                loc = getattr(node, 'location', None)
                line = loc.line if loc else 0
                col = loc.column if loc else 0
                self.call_graph[caller].add((callee, line, col))
        for ch in node.get_children():
            self._scan_calls_for_graph(ch, caller)

    def _detect_recursive_functions(self) -> None:
        """Detect functions that are recursive (can reach themselves via call graph)."""
        for func in self.known:
            if self._can_reach(func, func):
                self.recursive_funcs.add(func)

    def _can_reach(self, start: str, target: str, visited: Optional[set] = None) -> bool:
        """Check if start can reach target via the call graph."""
        if visited is None:
            visited = set()
        if start in visited:
            return False
        visited.add(start)
        for callee, _, _ in self.call_graph.get(start, set()):
            if callee == target:
                return True
            if self._can_reach(callee, target, visited):
                return True
        return False

    # -- Analysis Phase: Literal Callsites ----------------------------------

    def _collect_literal_callsites(self, tu: cx.TranslationUnit, source_file: str) -> None:
        
        for cur in tu.cursor.get_children():
            if not (cur.kind == cx.CursorKind.FUNCTION_DECL and cur.is_definition() and self._is_in_source(cur, source_file)):
                continue
            caller = cur.spelling
            body = next((c for c in cur.get_children() if c.kind == cx.CursorKind.COMPOUND_STMT), None)
            if body is None:
                continue
            self._scan_calls_for_callsites(body, caller)

    def _scan_calls_for_callsites(self, node: cx.Cursor, caller: str) -> None:
        """Recursively scan for ALL CALL_EXPR nodes."""
        if node.kind == cx.CursorKind.CALL_EXPR:
            callee = node.spelling
            if callee not in self.known:
                for ch in node.get_children():
                    self._scan_calls_for_callsites(ch, caller)
                return
            decl = self.known_decls.get(callee)
            if decl is None:
                for ch in node.get_children():
                    self._scan_calls_for_callsites(ch, caller)
                return
            params = [ch for ch in decl.get_children() if ch.kind == cx.CursorKind.PARM_DECL]
            children = list(node.get_children())
            if params and len(children) >= len(params):
                args = children[-len(params):]
            else:
                args = children[1:] if children and children[0].kind in (
                    cx.CursorKind.DECL_REF_EXPR,
                    cx.CursorKind.MEMBER_REF_EXPR,
                    cx.CursorKind.UNEXPOSED_EXPR,
                ) else children
            
            loc = getattr(node, 'location', None)
            line = loc.line if loc else 0
            col = loc.column if loc else 0
            cs_key = (caller, callee, line, col)
            self.literal_callsites[cs_key] = []
            
            for arg_idx, anode in enumerate(args):
                # Try to extract literal
                parsed = ast_extract_integer(anode)
                if parsed is not None:
                    # Literal argument
                    self.literal_callsites[cs_key].append((arg_idx, parsed))
                else:
                    # Variable argument: store the AST node itself for later analysis
                    self.literal_callsites[cs_key].append((arg_idx, anode))
        
        for ch in node.get_children():
            self._scan_calls_for_callsites(ch, caller)

    # -- Clone Generation -----------------------------------

    def _generate_clones(self, tu: cx.TranslationUnit, source_file: str) -> None:
        """Generate clones for all call-sites to isolate counters per call-site.
        
        Clones enable per-call-site counter variables and seeding, but share reversal
        budgets with the original.
        """
        for (caller, callee, line, col), call_args in self.literal_callsites.items():
            if not call_args:
                continue
            if callee in self.recursive_funcs:
                continue
            
            clone_name = f"{callee}_clone_{line}_{col}"
            self.clone_map[(callee, line, col)] = clone_name
            
            callee_decl = self.known_decls[callee]
            params = [ch for ch in callee_decl.get_children() if ch.kind == cx.CursorKind.PARM_DECL]
            
            # Create parameter key mappings for this clone
            self.clone_param_keys[clone_name] = {}
            for param_idx, pdecl in enumerate(params):
                orig_key = self._cursor_key(pdecl)
                cloned_key = f"{orig_key}#clone_{line}_{col}"
                self.clone_param_keys[clone_name][param_idx] = cloned_key
                
                # Create cloned counter variable with same budget as original
                if orig_key in self.counter_vars:
                    self.counter_vars[cloned_key] = {
                        'name': pdecl.spelling,
                        'reversals': self.counter_vars[orig_key].get('reversals', 0)
                    }
                    safe = self.declname_map.get(orig_key, pdecl.spelling)
                    safe_cloned = f"{safe}_clone_{line}_{col}"
                    self.declname_map[cloned_key] = safe_cloned



    # -- Seeding -------------------------------------------

    def _prescan_seeds(self, tu: cx.TranslationUnit, source_file: str) -> None:
        """Walk functions and mark any callee parameter declarations that
        will be seeded by literal arguments. Also record local decls that
        must be emitted in the caller so seeding assignments are legal.
        """
        for cur in tu.cursor.get_children():
            if not (cur.kind == cx.CursorKind.FUNCTION_DECL and cur.is_definition() and self._is_in_source(cur, source_file)):
                continue
            caller = cur.spelling
            # find body
            body = next((c for c in cur.get_children() if c.kind == cx.CursorKind.COMPOUND_STMT), None)
            if body is None:
                continue
            # Scan for CALL_EXPR with literal arguments
            self._scan_for_seeded_params(body, caller)
            # Additionally scan for simple literal assignments and VAR_DECL initialisers
            self._scan_assigns_recursive(body)

    def _scan_for_seeded_params(self, node: cx.Cursor, caller: str) -> None:
        """Recursively scan for CALL_EXPR nodes with literal arguments to seed."""
        if node.kind == cx.CursorKind.CALL_EXPR:
            name = node.spelling
            decl = self.known_decls.get(name)
            if decl is None:
                for ch in node.get_children():
                    self._scan_for_seeded_params(ch, caller)
                return
            params = [ch for ch in decl.get_children() if ch.kind == cx.CursorKind.PARM_DECL]
            children = list(node.get_children())
            if params and len(children) >= len(params):
                args = children[-len(params):]
            else:
                args = children[1:] if children and children[0].kind in (
                    cx.CursorKind.DECL_REF_EXPR,
                    cx.CursorKind.MEMBER_REF_EXPR,
                    cx.CursorKind.UNEXPOSED_EXPR,
                ) else children
            for param_idx, (pdecl, anode) in enumerate(zip(params, args)):
                parsed = ast_extract_integer(anode)
                if parsed is not None:
                    if name in self.recursive_funcs:
                        continue

                    pkey = self._cursor_key(pdecl)
                    loc = getattr(node, 'location', None)
                    line = loc.line if loc else 0
                    col = loc.column if loc else 0
                    
                    # check if this call-site is cloned
                    clone_key = (name, line, col)
                    if clone_key in self.clone_map:
                        # Use cloned parameter key
                        clone_name = self.clone_map[clone_key]
                        seeded_key = self.clone_param_keys[clone_name].get(param_idx, pkey)
                    else:
                        if loc and getattr(loc, 'file', None):
                            seeded_key = f"{pkey}@{caller}:{line}:{col}"
                        else:
                            seeded_key = f"{pkey}@{caller}:unknown"
                    self.seeded_vars.add(seeded_key)
                    # original parameter key marked as seeded for condition analysis variables
                    self.seeded_vars.add(pkey)
        
        for ch in node.get_children():
            self._scan_for_seeded_params(ch, caller)

    def _scan_assigns_recursive(self, node: cx.Cursor) -> None:
        """Recursively walk AST to find VAR_DECL initialisers with literal values.
        
        Marks variables initialized with literals as seeded so they get the
        reversal budget boost in the header emissions.
        """
    
        if node.kind == cx.CursorKind.VAR_DECL:
            name = getattr(node, 'spelling', None)
            if name:
                initialiser_val = None
                for child in node.get_children():
                    initialiser_val = self._find_int_literal_in_node(child)
                    if initialiser_val is not None:
                        break
                
                if initialiser_val is not None:
                    key = self._cursor_key(node)
                    if key in self.counter_vars:
                        self.seeded_vars.add(key)
        

        for ch in node.get_children():
            self._scan_assigns_recursive(ch)

    # -- Analysis Phase: Boolean Collection ----------------------------------

    def _collect_booleans(self, tu: cx.TranslationUnit, source_file: str) -> None:
        """Single unified pass to collect all boolean declarations (global and local).
        
        Uses semantic_parent to determine scope:
        - If parent is a FUNCTION_DECL, the boolean is local to that function
        - Otherwise, it's a global boolean
        
        This single AST pass replaces the need for separate global/local collection paths.
        """
        for cur in tu.cursor.get_children():
            if self._is_in_source(cur, source_file):
                self._walk_booleans_recursive(cur, source_file)

    def _walk_booleans_recursive(self, node: cx.Cursor, source_file: str) -> None:
        """Recursively walk AST to find and collect all boolean declarations.
        
        For each VAR_DECL or PARM_DECL with bool/_Bool type:
        - Walks semantic_parent chain to determine if it's local (parent is FUNCTION_DECL)
          or global (no function parent)
        - Stores in bool_decls with key: (bool_name, owner_proc_or_None)
        """
        try:
            kind = node.kind
        except Exception:
            kind = None
        if kind in (cx.CursorKind.VAR_DECL, cx.CursorKind.PARM_DECL):
            # try to detect `_Bool` / `bool` types
            try:
                cursor_type = getattr(node, 'type', None)
                type_string = cursor_type.get_canonical().spelling if cursor_type is not None else ''
            except Exception:
                type_string = getattr(node, 'type', '').__str__() if getattr(node, 'type', None) else ''
            if type_string and ('_Bool' in type_string or 'bool' in type_string):
                key = self._cursor_key(node)
                # determine owning procedure (if any) by walking semantic parents
                owner = None
                parent = getattr(node, 'semantic_parent', None)
                while parent is not None:
                    if getattr(parent, 'kind', None) == cx.CursorKind.FUNCTION_DECL and self._is_in_source(parent, source_file):
                        owner = parent.spelling
                        break
                    parent = getattr(parent, 'semantic_parent', None)
                self.bool_decls[key] = (node.spelling, owner)
        for ch in node.get_children():
            self._walk_booleans_recursive(ch, source_file)



    # -- Analysis Phase: Counter Variables & Guard Analysis ------------------

    def _infer_counter_vars(self, tu: cx.TranslationUnit, source_file: str) -> dict[str, dict]:
        """Path-sensitive reversal analysis using control flow graphs.
        
        Analyzes all variables that appear in conditions and calculates how many
        times their behaviour reverses (transitions from increasing to decreasing or vice versa).
        Variables are included in the output if reversals <= max_reversals.
        
        Returns dict mapping decl-key -> {'name': str, 'reversals': int}
        
        For each variable, the 'reversals' count represents the worst-case (maximum)
        number of reversals seen across any execution path through the program.
        """
        all_path_data: dict[str, list[dict]] = {}
        cond_vars: set[str] = set()


        for cur in tu.cursor.get_children():
            if not (cur.kind == cx.CursorKind.FUNCTION_DECL and cur.is_definition() and self._is_in_source(cur, source_file)):
                continue


            self._collect_condition_vars(cur, cond_vars)


            cfg_builder = CFGBuilder()
            cfg_builder.build_from_function(cur)
            analyser = ReversalAnalyser(cfg_builder, self)
            path_data = analyser.analyse()


            for var_key, path_infos in path_data.items():
                if var_key not in all_path_data:
                    all_path_data[var_key] = []
                all_path_data[var_key].extend(path_infos)
        
        result: dict[str, dict] = {}
        for vkey in cond_vars:
            path_infos = all_path_data.get(vkey, [])
            
            if not path_infos:
                reversals = 0
            else:
                if any(info['reversals'] == -1 for info in path_infos):
                    reversals = -1
                else:
                    # worst case taken per path for reversals
                    reversals = max(info['reversals'] for info in path_infos)
            
            # exclude if marked as excluded or if exceeds reversal budget
            if reversals == -1 or reversals > self.max_reversals:
                continue
            
            
            if isinstance(vkey, tuple):
                vname = vkey[1]
                key = vkey[0]
            else:
                key = vkey
                # extract the actual variable name from USR-like key (format: c:file@line@F@func@name)
                vname = vkey.split("@")[-1] 
            
            result[key] = {"name": vname, "reversals": reversals}
        
        return result

    def _collect_condition_vars(self, cur: cx.Cursor, cond_vars: set[str]) -> None:
        k = cur.kind
        if k in (cx.CursorKind.IF_STMT, cx.CursorKind.WHILE_STMT, cx.CursorKind.DO_STMT, cx.CursorKind.FOR_STMT):
            children = list(cur.get_children())
            cond = None
            if k == cx.CursorKind.IF_STMT:
                cond = children[0] if children else None
            elif k == cx.CursorKind.WHILE_STMT:
                cond = children[0] if len(children) > 0 else None
            elif k == cx.CursorKind.DO_STMT:
                cond = children[1] if len(children) > 1 else None
            elif k == cx.CursorKind.FOR_STMT and len(children) >= 2:
                cond = children[-2]
            self._collect_all_guard_vars(cond, cond_vars)
        for child in cur.get_children():
            self._collect_condition_vars(child, cond_vars)

    def _collect_all_guard_vars(self, cond: Optional[cx.Cursor], cond_vars: set[str]) -> None:
        if cond is None:
            return

        # Handle wrapper nodes
        if cond.kind == cx.CursorKind.UNEXPOSED_EXPR:
            children = list(cond.get_children())
            if len(children) == 1:
                self._collect_all_guard_vars(children[0], cond_vars)
            return

        if cond.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(cond)
            if parts is not None:
                left_expr, op, right_expr = parts
                
                # Logical operators
                if op in ("&&", "||"):
                    self._collect_all_guard_vars(left_expr, cond_vars)
                    self._collect_all_guard_vars(right_expr, cond_vars)
                    return
                
                # Comparison operators
                if op in ["<=", ">=", "==", "!=", "<", ">"]:
                    left_var = ast_extract_variable(left_expr)
                    right_int = ast_extract_integer(right_expr)
                    if left_var is not None and right_int is not None:
                        var_key = self._resolve_decl_key_in_expr(cond, left_var)
                        cond_vars.add(var_key)
                        return
                    
                    # constant op var
                    left_int = ast_extract_integer(left_expr)
                    right_var = ast_extract_variable(right_expr)
                    if left_int is not None and right_var is not None:
                        var_key = self._resolve_decl_key_in_expr(cond, right_var)
                        cond_vars.add(var_key)
                        return
                    
                    #  linear form 
                    left_lin = self._extract_linear_expr(left_expr)
                    if left_lin is not None:
                        var, _ = left_lin
                        var_key = self._resolve_decl_key_in_expr(cond, var)
                        cond_vars.add(var_key)
                        return
                    
                    right_lin = self._extract_linear_expr(right_expr)
                    if right_lin is not None:
                        var, _ = right_lin
                        var_key = self._resolve_decl_key_in_expr(cond, var)
                        cond_vars.add(var_key)
                        return

    def _condition_to_guard(self, cond: Optional[cx.Cursor]) -> str:
        """Convert a condition AST node to a guard string"""
        result = self._condition_to_guard_ast(cond)
        if result is None:
            return "??"
        
        # Add brackets if not already formatted as boolean guard
        if not result.startswith("{"):
            return f"[{result}]"
        return result
    
    def _condition_to_guard_ast(self, cond: Optional[cx.Cursor]) -> Optional[str]:
        """Recursively convert condition to guard string.
        
        Handles:
        - Simple comparisons: n == 1 -> "n == 1"
        - Compound conditions: n == 1 && x > 5 -> "n == 1 && x > 5"
        - Boolean guards: flag -> "{flag}" or !flag -> "{!flag}"
        """
        if cond is None:
            return None
        
        # handle wrapper nodes like UNEXPOSED_EXPR
        if cond.kind == cx.CursorKind.UNEXPOSED_EXPR:
            children = list(cond.get_children())
            if len(children) == 1:
                return self._condition_to_guard_ast(children[0])
            return None
        
        # handle logical operators (&&, ||)
        if cond.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(cond)
            if parts is not None:
                left_expr, op, right_expr = parts
                

                if op in ("&&", "||"):
                    left_guard = self._condition_to_guard_ast(left_expr)
                    right_guard = self._condition_to_guard_ast(right_expr)
                    if left_guard is not None and right_guard is not None:
                        return f"{left_guard} {op} {right_guard}"
                    return None
                
                # Comparison operators: extract guard
                if op in ["<=", ">=", "==", "!=", "<", ">"]:
                    left_var = ast_extract_variable(left_expr)
                    right_int = ast_extract_integer(right_expr)
                    
                    if left_var is not None and right_int is not None:
                        var_key = self._resolve_decl_key_in_expr(cond, left_var)
                        var_key = self.get_remapped_key(var_key)
                        safe = self.declname_map.get(var_key, left_var)
                        return f"{safe} {op} {right_int}"
                    
                    # Try flipped: const op var
                    left_int = ast_extract_integer(left_expr)
                    right_var = ast_extract_variable(right_expr)
                    
                    if left_int is not None and right_var is not None:
                        var_key = self._resolve_decl_key_in_expr(cond, right_var)
                        var_key = self.get_remapped_key(var_key)
                        safe = self.declname_map.get(var_key, right_var)
                        flipped_op = self._flip_comparison(op)
                        return f"{safe} {flipped_op} {left_int}"
                    
                    # Try linear form
                    left_lin = self._extract_linear_expr(left_expr)
                    right_lin = self._extract_linear_expr(right_expr)
                    
                    if left_lin is not None:
                        var, offset = left_lin
                        right_int = ast_extract_integer(right_expr)
                        if right_int is not None:
                            var_key = self._resolve_decl_key_in_expr(cond, var)
                            var_key = self.get_remapped_key(var_key)
                            safe = self.declname_map.get(var_key, var)
                            return f"{safe} {op} {right_int - offset}"
                    
                    if right_lin is not None:
                        var, offset = right_lin
                        left_int = ast_extract_integer(left_expr)
                        if left_int is not None:
                            var_key = self._resolve_decl_key_in_expr(cond, var)
                            var_key = self.get_remapped_key(var_key)
                            safe = self.declname_map.get(var_key, var)
                            return f"{safe} {self._flip_comparison(op)} {left_int - offset}"
        
        # Handle unary negation: !ident
        if cond.kind == cx.CursorKind.UNARY_OPERATOR:
            parts = ast_get_unary_operator_parts(cond)
            if parts is not None:
                op, operand = parts
                if op == "!":
                    var = ast_extract_variable(operand)
                    if var is not None:
                        key = self._resolve_decl_key_in_expr(cond, var)
                        key = self.get_remapped_key(key)
                        if key in self.bool_decls:
                            safe = self.declname_map.get(key, var)
                            return f"{{!{safe}}}"
        
        # Handle plain identifier (boolean)
        if cond.kind == cx.CursorKind.DECL_REF_EXPR:
            var = ast_extract_variable(cond)
            if var is not None:
                key = self._resolve_decl_key_in_expr(cond, var)
                key = self.get_remapped_key(key)
                if key in self.bool_decls:
                    safe = self.declname_map.get(key, var)
                    return f"{{{safe}}}"
        
        return None

    def _extract_linear_expr(self, expr: Optional[cx.Cursor]) -> Optional[tuple[str, int]]:
        """Extract variable and offset from linear expressions like 'x + 5' or 'x - 3'."""
        if expr is None:
            return None
        
        var = ast_extract_variable(expr)
        if var is not None:
            return (var, 0)
        
        # Binary operation: var +/- const or const +/- var
        if expr.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(expr)
            if parts is not None:
                left, op, right = parts
                
                if op == "+":
                    # x + K or K + x
                    left_var = ast_extract_variable(left)
                    right_int = ast_extract_integer(right)
                    if left_var is not None and right_int is not None:
                        return (left_var, right_int)
                    
                    left_int = ast_extract_integer(left)
                    right_var = ast_extract_variable(right)
                    if left_int is not None and right_var is not None:
                        return (right_var, left_int)
                
                elif op == "-":
                    # x - K (but not K - x, which would be unnatural)
                    left_var = ast_extract_variable(left)
                    right_int = ast_extract_integer(right)
                    if left_var is not None and right_int is not None:
                        return (left_var, -right_int)
        
        return None

    # -- AST Handler Functions -----------------------------------

    def _proc(self, cur: cx.Cursor, emit_as_clone: Optional[str] = None) -> None:
        name = cur.spelling
        if emit_as_clone:
            self._emitting_clone = True
            self.current_proc_name = emit_as_clone
            self.current_clone_for_param_key = emit_as_clone
            proc_name_to_emit = emit_as_clone
        else:
            self._emitting_clone = False
            self.current_proc_name = name
            self.current_clone_for_param_key = None
            proc_name_to_emit = name
        body = next(
            (c for c in cur.get_children() if c.kind == cx.CursorKind.COMPOUND_STMT),
            None,
        )
        stmts = list(body.get_children()) if body else []

        self.out.w(f"procedure {proc_name_to_emit}()")
        # Emit any procedure-local boolean declarations
        locals_list = [(k, v[0]) for k, v in self.bool_decls.items() if v[1] == proc_name_to_emit]
        if locals_list:
            self.out.indent()
            for k, bname in locals_list:
                safe = self.declname_map.get(k)
                if safe is None:
                    safe = ''.join(c if (c.isalnum() or c == '_') else '_' for c in bname)
                    if safe in set(self.declname_map.values()):
                        safe = safe + '_b'
                    self.declname_map[k] = safe
                self.out.w(f"bool {safe}")
            self.out.dedent()
        if not stmts:
            self.out.w("    skip;")
            self.out.blank()
            return

        self.out.w("begin")
        self.out.indent()
        before = len(self.out._lines)
        for s in stmts:
            self._stmt(s)
        if len(self.out._lines) == before:
            self.out.w("skip;")
        self.out.dedent()
        self.out.w("end;")
        self.out.blank()
        # clear current proc
        self.current_proc_name = None
        self._emitting_clone = False
        self.current_clone_for_param_key = None


    def _stmt(self, cur: cx.Cursor) -> None:
        k = cur.kind

        if k == cx.CursorKind.COMPOUND_STMT:
            for child in cur.get_children():
                self._stmt(child)

        elif k == cx.CursorKind.IF_STMT:
            self._if(cur)

        elif k in (cx.CursorKind.WHILE_STMT, cx.CursorKind.FOR_STMT, cx.CursorKind.DO_STMT):
            self._loop(cur)

        elif k == cx.CursorKind.RETURN_STMT:
            # still emit any alloc/free hidden in the return expression
            self._scan_calls(cur)
            self.out.w("return;")

        elif k == cx.CursorKind.DECL_STMT:
            # Unwrap DECL_STMT to process contained VAR_DECL/PARM_DECL
            for child in cur.get_children():
                self._emit_counter_updates(child)
                self._scan_calls(child)

        else:
            self._emit_counter_updates(cur)

            self._scan_calls(cur)

    def _if(self, cur: cx.Cursor) -> None:
        children = list(cur.get_children())
        # children: [condition?, then, else?]
        cond      = children[0] if len(children) > 0 else None
        then_cur  = children[1] if len(children) > 1 else None
        else_cur  = children[2] if len(children) > 2 else None


        if cond is not None:
            self._scan_calls(cond)

        guard = self._condition_to_guard(cond)
        self.out.w(f"if {guard} then")

        self._block_or_skip(then_cur)

        if else_cur is not None:
            self.out.w("else")
            self._block_or_skip(else_cur)

    def _loop(self, cur: cx.Cursor) -> None:
        k        = cur.kind
        children = list(cur.get_children())

        cond = None
        if k == cx.CursorKind.WHILE_STMT:
            cond = children[0] if len(children) > 0 else None
        elif k == cx.CursorKind.DO_STMT:
            cond = children[1] if len(children) > 1 else None
        elif k == cx.CursorKind.FOR_STMT and len(children) >= 2:
            # For loops usually have init/cond/inc/body; cond is often penultimate.
            cond = children[-2]

        self.out.w(f"while {self._condition_to_guard(cond)} do")

        if k == cx.CursorKind.WHILE_STMT:
            # [condition, body]
            cond = children[0] if len(children) > 0 else None
            body = children[1] if len(children) > 1 else None
            if cond is not None:
                self._scan_calls(cond)
            self._block_or_skip(body)

        elif k == cx.CursorKind.DO_STMT:
            # [body, condition]
            body = children[0] if len(children) > 0 else None
            cond = children[1] if len(children) > 1 else None
            self._block_or_skip(body)
            if cond is not None:
                self._scan_calls(cond)

        elif k == cx.CursorKind.FOR_STMT:
            if children:
                # emit calls from init/cond/increment 
                for c in children[:-1]:
                    self._emit_counter_updates(c)
                    self._scan_calls(c)
                self._block_or_skip(children[-1])
            else:
                self.out.indent()
                self.out.w("skip;")
                self.out.dedent()

    # -- Code Generation Phase: Blocks and Calls ----------------------------

    def _block_or_skip(self, cur: Optional[cx.Cursor]) -> None:
        if cur is None:
            self.out.indent()
            self.out.w("skip;")
            self.out.dedent()
        else:
            self._block(cur)

    def _block(self, cur: cx.Cursor) -> None:
        if cur.kind == cx.CursorKind.COMPOUND_STMT:
            stmts = list(cur.get_children())
            if not stmts:
                self.out.indent()
                self.out.w("skip;")
                self.out.dedent()
                return

            if len(stmts) == 1:
                self.out.indent()
                before = len(self.out._lines)
                self._stmt(stmts[0])
                if len(self.out._lines) == before:
                    self.out.w("skip;")
                self.out.dedent()
            else:
                self.out.w("begin")
                self.out.indent()
                before = len(self.out._lines)
                for s in stmts:
                    self._stmt(s)
                if len(self.out._lines) == before:
                    self.out.w("skip;")
                self.out.dedent()
                self.out.w("end;")
        else:
            self.out.indent()
            before = len(self.out._lines)
            self._stmt(cur)
            if len(self.out._lines) == before:
                self.out.w("skip;")
            self.out.dedent()

    def _scan_calls(self, cur: cx.Cursor) -> None:
        """
        Recursively walk an expression subtree.
        At each CALL_EXPR: first recurse into its arguments (left-to-right
        evaluation order), then emit the call itself.
        """
        if cur.kind == cx.CursorKind.CALL_EXPR:
            for child in cur.get_children():
                self._scan_calls(child)
            self._call(cur)
            return
        for child in cur.get_children():
            self._scan_calls(child)

    def _call(self, cur: cx.Cursor) -> None:
        name = cur.spelling
        for action_name, action_config in self.tracked_actions.items():
            if name in action_config["functions"]:
                self.out.w(f"echo {action_config['echo']};")
                return
        
        if name in self.known:
            loc = getattr(cur, 'location', None)
            line = loc.line if loc else 0
            col = loc.column if loc else 0
            clone_key = (name, line, col)
            
            # determine which function to call and what seeding keys to use
            if clone_key in self.clone_map:
                # call the cloned version and use cloned parameter keys
                call_name = self.clone_map[clone_key]
                clone_name = call_name
                param_keys_map = self.clone_param_keys.get(clone_name, {})
            else:
                # call the original function
                call_name = name
                clone_name = None
                param_keys_map = {}
            
            decl = self.known_decls.get(name)
            param_decls: list[cx.Cursor] = []
            if decl is not None:
                for ch in decl.get_children():
                    if ch.kind == cx.CursorKind.PARM_DECL:
                        param_decls.append(ch)

            children = list(cur.get_children())
            # choose trailing nodes as arguments if parameters known
            if param_decls and len(children) >= len(param_decls):
                args = children[-len(param_decls):]
            else:
                args = children[1:] if children and children[0].kind in (
                    cx.CursorKind.DECL_REF_EXPR,
                    cx.CursorKind.MEMBER_REF_EXPR,
                    cx.CursorKind.UNEXPOSED_EXPR,
                ) else children


            if name not in self.recursive_funcs:
                for param_idx, (pdecl, anode) in enumerate(zip(param_decls, args)):

                    parsed = ast_extract_integer(anode)
                    if parsed is not None:
                        pkey = self._cursor_key(pdecl)

                        seeded_key = param_keys_map.get(param_idx, pkey)
                        
                        safe = self.declname_map.get(seeded_key, pdecl.spelling)
                        if parsed >= 0:
                            self.out.w(f"{safe} += {parsed};")
                        else:
                            self.out.w(f"{safe} -= {abs(parsed)};")
                        self.seeded_vars.add(seeded_key)

            self.out.w(f"{call_name}();")



    def _emit_counter_updates(self, cur: cx.Cursor) -> None:
        if cur.kind == cx.CursorKind.VAR_DECL:
            name = getattr(cur, 'spelling', None)
            if name:
                key = self._cursor_key(cur)
                
                # search for initialiser
                initialiser_val = None
                for child in cur.get_children():
                    initialiser_val = self._find_int_literal_in_node(child)
                    if initialiser_val is not None:
                        break
                

                if key in self.bool_decls and initialiser_val is not None:
                    safe = self.declname_map.get(key, name)
                    self.out.w(f"{safe} = {initialiser_val};")
                    return
                
                if key in self.counter_vars and initialiser_val is not None:
                    safe = self.declname_map.get(key, name)
                    if initialiser_val >= 0:
                        self.out.w(f"{safe} += {initialiser_val};")
                    else:
                        self.out.w(f"{safe} -= {abs(initialiser_val)};")
                    return

        update = self._classify_counter_update(cur)
        if update is not None:
            # update: (var_key, kind)
            var_key, kind = update
            # Remap parameter keys if in a cloned procedure
            var_key = self.get_remapped_key(var_key)
            # choose safe emitted name when available
            safe = self.declname_map.get(var_key, "")
            if var_key in self.counter_vars:
                if cur.kind == cx.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
                    parts = ast_get_compound_assign_parts(cur)
                    if parts is not None:
                        _, op, rhs_expr = parts
                        amount = ast_extract_integer(rhs_expr)
                        if amount is not None:
                            if op == "+=":
                                if amount > 0:
                                    self.out.w(f"{safe} += {amount};")
                                elif amount < 0:
                                    self.out.w(f"{safe} -= {abs(amount)};")
                                else:
                                    pass  
                                return
                            elif op == "-=":
                                if amount > 0:
                                    self.out.w(f"{safe} -= {amount};")
                                elif amount < 0:
                                    self.out.w(f"{safe} += {abs(amount)};")
                                else:
                                    pass  
                            return
                
                # fallback to increment/decrement for unary operators (++ or --)
                if kind == "inc":
                    self.out.w(f"{safe}++;")
                elif kind == "dec":
                    self.out.w(f"{safe}--;")
            return


        if cur.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(cur)
            if parts is not None and parts[1] == "=":
                lhs_expr, _, rhs_expr = parts
                lhs = ast_extract_variable(lhs_expr)
                
                # seed if numerical assignment to variable
                if lhs is not None:
                    parsed = ast_extract_integer(rhs_expr)
                    if parsed is not None:
                        key = self._resolve_decl_key_in_expr(cur, lhs)
                        key = self.get_remapped_key(key)
                        if key in self.counter_vars:
                            safe = self.declname_map.get(key, lhs)
                            if parsed >= 0:
                                self.out.w(f"{safe} += {parsed};")
                            else:
                                self.out.w(f"{safe} -= {abs(parsed)};")
                            # record seeded var 
                            self.seeded_vars.add(key)
                            return

        for child in cur.get_children():
            self._emit_counter_updates(child)

    def _classify_counter_update(
        self,
        cur: cx.Cursor,
    ) -> Optional[tuple[str, Literal["inc", "dec", "neutral", "unknown"]]]:
        """Classify counter updates (x++, x+=5, etc.)"""
        
        # Case 1: Unary operators (x++, x--)
        if cur.kind == cx.CursorKind.UNARY_OPERATOR:
            parts = ast_get_unary_operator_parts(cur)
            if parts is None:
                return None
            
            op, operand = parts
            var = ast_extract_variable(operand)
            
            if var is None:
                return None
            
            var_key = self._resolve_decl_key_in_expr(cur, var)
            
            if op == "++":
                return (var_key, "inc")
            elif op == "--":
                return (var_key, "dec")
        
        # Case 2: Compound assignment (x += 5, x -= 3, etc.)
        elif cur.kind == cx.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
            parts = ast_get_compound_assign_parts(cur)
            if parts is None:
                return None
            
            var_expr, op, rhs_expr = parts
            var = ast_extract_variable(var_expr)
            
            if var is None:
                return None
            
            var_key = self._resolve_decl_key_in_expr(cur, var)
            amount = ast_extract_integer(rhs_expr)
            
            if amount is None:
                return (var_key, "unknown")
            
            if op == "+=":
                if amount > 0:
                    return (var_key, "inc")
                elif amount < 0:
                    return (var_key, "dec")
                else:
                    return (var_key, "neutral")
            elif op == "-=":
                if amount > 0:
                    return (var_key, "dec")
                elif amount < 0:
                    return (var_key, "inc")
                else:
                    return (var_key, "neutral")
            else:
                return (var_key, "unknown")
        
        # Case 3: Binary assignment (x = x + 5, x = 5 + x, x = constant)
        elif cur.kind == cx.CursorKind.BINARY_OPERATOR:
            parts = ast_get_binary_operator_parts(cur)
            if parts is None or parts[1] != "=":
                return None
            
            lhs_expr, _, rhs_expr = parts
            var = ast_extract_variable(lhs_expr)
            
            if var is None:
                return None
            
            var_key = self._resolve_decl_key_in_expr(cur, var)
            
            # x = x + constant
            if rhs_expr.kind == cx.CursorKind.BINARY_OPERATOR:
                rhs_parts = ast_get_binary_operator_parts(rhs_expr)
                if rhs_parts is not None:
                    rhs_left, rhs_op, rhs_right = rhs_parts
                    
                    # Check if this is x = x + K or x = K + x
                    left_var = ast_extract_variable(rhs_left)
                    right_var = ast_extract_variable(rhs_right)
                    left_int = ast_extract_integer(rhs_left)
                    right_int = ast_extract_integer(rhs_right)
                    
                    # x = x + K
                    if left_var == var and right_int is not None:
                        if rhs_op == "+":
                            if right_int > 0:
                                return (var_key, "inc")
                            elif right_int < 0:
                                return (var_key, "dec")
                            else:
                                return (var_key, "neutral")
                        elif rhs_op == "-":
                            if right_int > 0:
                                return (var_key, "dec")
                            elif right_int < 0:
                                return (var_key, "inc")
                            else:
                                return (var_key, "neutral")
                    
                    # x = K + x
                    elif right_var == var and left_int is not None:
                        if rhs_op == "+":
                            if left_int > 0:
                                return (var_key, "inc")
                            elif left_int < 0:
                                return (var_key, "dec")
                            else:
                                return (var_key, "neutral")
            
            # x = constant
            amount = ast_extract_integer(rhs_expr)
            if amount is not None:
                return (var_key, "neutral")
            
            # Subcase 3c: x = variable
            if ast_extract_variable(rhs_expr) == var:
                return (var_key, "neutral")
            
            return (var_key, "unknown")
        
        return None

    # -- Utility & Helper Methods -------------------------------------------

    def _is_in_source(self, cur: cx.Cursor, source_file: str) -> bool:
        """Check if a cursor is from the source file (not from includes)."""
        return (cur.location.file is not None
                and cur.location.file.name == source_file)

    def _cursor_key(self, decl: cx.Cursor) -> str:
        """Return a stable key for a declaration cursor (USR if available,
        else a file:line:col:name fallback)."""
        try:
            usr = decl.get_usr()
        except Exception:
            usr = None
        if usr:
            return usr
        loc = getattr(decl.location, 'file', None)
        if loc is not None:
            return f"{loc.name}:{decl.location.line}:{decl.location.column}:{decl.spelling}"
        return f"name::{decl.spelling}"

    def _resolve_decl_key_in_expr(self, expr: Optional[cx.Cursor], name: str) -> str:
        """Try to resolve a declaration key for `name` within the given
        expression subtree. If no DeclRefExpr referencing a declaration is
        found, fall back to a name-based key."""
        if expr is None:
            return f"name::{name}"

        stack = [expr]
        while stack:
            node = stack.pop()
            try:
                if getattr(node, 'kind', None) == cx.CursorKind.DECL_REF_EXPR and getattr(node, 'referenced', None):
                    return self._cursor_key(node.referenced)
            except Exception:
                pass
            for ch in node.get_children():
                stack.append(ch)
        # fallback to name-based key when no referenced decl was found
        return f"name::{name}"

    def _flip_comparison(self, op: str) -> str:
        return {
            "<": ">",
            ">": "<",
            "<=": ">=",
            ">=": "<=",
            "==": "==",
            "!=": "!=",
        }.get(op, op)

    def _find_int_literal_in_node(self, node: cx.Cursor) -> Optional[int]:
        """Recursively find integer literal in a node and its children using pure AST."""
        # direct extraction
        val = ast_extract_integer(node)
        if val is not None:
            return val
        # Recurse to children
        for ch in node.get_children():
            v = self._find_int_literal_in_node(ch)
            if v is not None:
                return v
        return None

    def _dump_ast_to_file(self, tu: cx.TranslationUnit, output_file: str) -> None:
        """Dump the AST structure to a file."""
        with open(output_file, 'w') as f:
            f.write(f"AST Dump for: {tu.spelling}\n")
            f.write("=" * 80 + "\n\n")
            self._dump_ast_node(tu.cursor, f, depth=0)
    
    def _dump_ast_node(self, cursor: cx.Cursor, f, depth: int = 0) -> None:
        """Recursively dump AST node structure."""
        indent = "  " * depth
        kind = cursor.kind.name
        spelling = cursor.spelling or ""
        loc = cursor.location
        location_str = f"{loc.file.name if loc.file else 'unknown'}:{loc.line}:{loc.column}" if loc.file else "unknown"
        
    
        node_str = f"{indent}[{kind}]"
        if spelling:
            node_str += f" {spelling}"
        node_str += f"  @ {location_str}"
        
        f.write(node_str + "\n")
        

        for child in cursor.get_children():
            self._dump_ast_node(child, f, depth + 1)



# -- CLI -----------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Translate C to .prog format"
    )
    parser.add_argument("input", help="C source file to translate")
    parser.add_argument(
        "--entry", default=None,
        help="Entry function name (default: main)",
    )
    parser.add_argument(
        "--alloc", default=None,
        help="Extra names to track as 'malloc' action, comma-separated (added to built-in set)",
    )
    parser.add_argument(
        "--free", default=None,
        help="Extra names to track as 'free' action, comma-separated (added to built-in set)",
    )
    parser.add_argument(
        "--clang-args", default="",
        help='Extra flags passed to clang, e.g. --clang-args="-I/usr/include/linux"',
    )
    parser.add_argument(
        "--output", default=None,
        help="Output file (default: stdout)",
    )
    parser.add_argument(
        "--constraints",
        default=None,
        help=(
            "Constraint strings comma-separated (e.g., 'malloc != free,malloc > free'). "
            f"Default from config: {','.join(DEFAULT_CONSTRAINTS['constraints'])}"
        ),
    )
    parser.add_argument(
        "--max-reversals",
        type=int,
        default=None,
        help=(
            "Maximum number of reversals allowed for counter variables. "
            "0 = strictly monotone only, 1 = allow one reversal, etc. "
            f"(default from config: {DEFAULT_CONSTRAINTS['max_reversals']})"
        ),
    )
    parser.add_argument(
        "--dump-ast",
        action="store_true",
        help="Dump the parsed AST structure to a file for inspection (optional, for debugging)",
    )
    args = parser.parse_args()

    # If the input is already a .prog file, skip C parsing and emit/copy it.
    if str(args.input).lower().endswith('.prog'):
        prog_path = Path(args.input)
        if not prog_path.exists():
            raise SystemExit(f"Input .prog file not found: {prog_path}")
        content = prog_path.read_text()
        if args.output:
            Path(args.output).write_text(content)
            return
        else:
            print(content)
            return

    # Build tracked_actions starting from defaults
    # Make sure we have TRACKED_ACTIONS available (imported from modelChecker or fallback)
    tracked_actions = {
        action_name: {
            "functions": set(config["functions"]),
            "echo": config["echo"]
        }
        for action_name, config in TRACKED_ACTIONS.items()
    }
    
    
    if args.constraints:
        constraints = [c.strip() for c in args.constraints.split(",")]
    else:
        constraints = DEFAULT_CONSTRAINTS["constraints"]
    max_reversals = args.max_reversals if args.max_reversals is not None else DEFAULT_CONSTRAINTS["max_reversals"]

    clang_flags = args.clang_args.split() if args.clang_args else []

    if not any(f.startswith("-std=") for f in clang_flags):
        clang_flags.insert(0, "-std=gnu11")

    index = cx.Index.create()
    tu = index.parse(
        args.input,
        args=clang_flags,
        options=cx.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD,
    )

    gen = ProgGen(
        tracked_actions=tracked_actions,
        constraints=constraints,
        max_reversals=max_reversals,
    )

    result = gen.generate(tu, entry=args.entry, output_path=args.output, dump_ast=args.dump_ast)

    if args.output:
        with open(args.output, "w") as f:
            f.write(result + "\n")
    else:
        print(result)


if __name__ == "__main__":
    main()
