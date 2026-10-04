#!/usr/bin/env python3
"""
SMT Model Trace Decoder
Reconstructs execution traces from SMT solver models using CFG and debugging mappings
"""

import re
import io
import argparse
import sys
from contextlib import redirect_stdout
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple, Optional


def _extract_base_name(source_name: str) -> str:
    """Extract the primary nonterminal name (e.g., v_caller_0_pd0) from a source expression"""
    if not source_name:
        return source_name
    # For tuples like ((v_q_pd0,1,0),v_caller_0_pd0,v_q_pd0,1,0), extract the second element
    match = re.search(r'\(v_[^,]+_\d+_pd\d+,\d+,\d+\),(v_[^,]+_\d+_pd\d+)', source_name)
    if match:
        return match.group(1)
    # For simple names like v_caller_0_pd0
    match = re.search(r'(v_[A-Za-z_]\w*_\d+_pd\d+)', source_name)
    if match:
        return match.group(1)
    return source_name


def _is_callee(nt: str) -> bool:
    """Return True if this nonterminal is a fresh function entry (pc=0), i.e. a callee."""
    # Matches patterns like v_foo_0_pd0 or ((v_q_pd0,N,0),v_foo_0_pd0,...)
    return bool(re.search(r'v_[A-Za-z_]\w*_0_pd\d+', nt))


class TraceDecoder:
    # --------------- INITIALISATION ---------------------
    
    def __init__(self, model_file: str, debug_file: str, cfg_file: str, source_file: Optional[str] = None, tracked_actions: Optional[Dict[str, Dict]] = None):
        # Prevent writing bytecode cache files when importing this module.
        sys.dont_write_bytecode = True
        self.model_file = model_file
        self.debug_file = debug_file
        self.cfg_file = cfg_file
        self.source_file = source_file
        self.tracked_actions = tracked_actions
        self.action_echos = [config["echo"] for config in tracked_actions.values()] if tracked_actions else []
        
        self.nonterminals = {}
        self.terminals = {}
        self.y_transition_info = {}
        self.fired_rules = []
        self.terminal_counts = {}
        

        self.rules_by_source: Dict[str, List[int]] = defaultdict(list)
        self.rule_rhs_nonterminals: Dict[int, List[str]] = {}
        
        self._parse_debug_file(debug_file)
        self._parse_model(model_file)
        

        self.cfg_nonterminals = []
        self.cfg_terminals = []
        self.cfg_transitions = []
        self._parse_cfg(cfg_file)
    
    # ---------------- INPUT PARSING ------------------
    
    def _parse_model(self, filepath: str) -> None:
        """Parse SMT model and extract fired rules and terminal counts"""
        fired_rules = []
        terminal_counts = {}
        
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Match (define-fun varname () Int value)
        pattern = r'\(define-fun\s+(\w+)\s+\(\)\s+Int\s+(-?\d+)\)'
        for match in re.finditer(pattern, content):
            var_name = match.group(1)
            value = int(match.group(2))
            
            # Extract fired rules (y_* > 0)
            if var_name.startswith('y_'):
                rule_num = int(var_name.split('_')[1])
                if value > 0:
                    fired_rules.append((rule_num, value))
            
            # Extract terminal counts (x_t_* > 0)
            elif var_name.startswith('x_t_') and value > 0:
                idx = int(var_name.split('_')[2])
                if idx in self.terminals:
                    terminal_counts[self.terminals[idx]] = value
        

        self.fired_rules = sorted(fired_rules, key=lambda item: item[0])
        self.terminal_counts = terminal_counts
    
    def _parse_debug_file(self, filepath: str):
        """Parse debugging.txt to get nonterminal and terminal mappings using regex"""
        if not filepath:
            return
            
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Pattern to extract name and key from lines like "name 123"
        line_pattern = r'(.+?)\s+(\d+)'
        
        # Extract nonterminals section
        nont_match = re.search(
            r'Printing Nonterminal Name and Key pairs\s*(.*?)(?=Printing Terminal|$)',
            content,
            re.DOTALL
        )
        if nont_match:
            section = nont_match.group(1)
            for match in re.finditer(line_pattern, section):
                name = match.group(1).strip()
                key = int(match.group(2))
                self.nonterminals[key] = name
        
        # Extract terminals section
        term_match = re.search(
            r'Printing Terminal Name and Key pairs\s*(.*?)$',
            content,
            re.DOTALL
        )
        if term_match:
            section = term_match.group(1)
            for match in re.finditer(line_pattern, section):
                name = match.group(1).strip()
                key = int(match.group(2))
                self.terminals[key] = name
    
    def _parse_cfg(self, filepath: str):
        """Parse debugging2.txt to get the Context-Free Grammar using bracket matching"""
        with open(filepath, 'r') as f:
            content = f.read()
        
        # find cg([ and extract the three main lists
        start_pos = content.find('cg([')
        if start_pos == -1:
            print("cfg not found")
            return
        
        # extract the content between cg( and the final n(start))
        pos = start_pos + 3  # skip 'cg('
        depth = 0
        list_contents = []
        current_list = []
        
        for i in range(pos, len(content)):
            char = content[i]
            
            if char == '[':
                depth += 1
                if depth == 1:
                    current_list = []
                else:
                    current_list.append(char)
            elif char == ']' and depth > 0:
                depth -= 1
                if depth == 0:
                    list_contents.append(''.join(current_list))
                    current_list = []
                    if len(list_contents) >= 3:
                        break
                else:
                    current_list.append(char)
            elif depth > 0:
                current_list.append(char)
        
        if len(list_contents) >= 3:
            nont_str, term_str, trans_str = list_contents[0], list_contents[1], list_contents[2]
            
            self.cfg_nonterminals = self._parse_prolog_list(nont_str)
            self.cfg_terminals = self._parse_prolog_list(term_str)
            self.cfg_transitions = self._parse_prolog_list(trans_str)
            self.y_transition_info = self._build_y_transition_mapping()
    

    
    def _parse_prolog_list(self, list_str: str) -> List[str]:
        items = []
        depth = 0
        current_item = []
        
        for char in list_str:
            if char in '([{':
                depth += 1
                current_item.append(char)
            elif char in ')]}':
                depth -= 1
                current_item.append(char)
            elif char == ',' and depth == 0:
                item = ''.join(current_item).strip()
                if item:
                    items.append(item)
                current_item = []
            else:
                current_item.append(char)
        
        # Add the last item
        item = ''.join(current_item).strip()
        if item:
            items.append(item)
        
        return items
    
    # ------------CFG PROCESSING & GRAMMAR INDEXING -----------------
    
    def _parse_transition(self, trans_str: str) -> Tuple[str, List[str]]:
        """Parse transition structure: extract source nonterminal and raw RHS alternatives from tran(n(Source),[RHS...])."""
        prefix = 'tran(n('
        if not trans_str.startswith(prefix):
            return "", []

        source_start = len(prefix)
        paren_depth = 1
        split_idx = -1

        for idx in range(source_start, len(trans_str) - 1):
            char = trans_str[idx]
            if char == '(':
                paren_depth += 1
            elif char == ')':
                paren_depth -= 1
            elif char == ',' and paren_depth == 0 and trans_str[idx + 1] == '[':
                split_idx = idx
                break

        if split_idx == -1:
            return "", []

        source = trans_str[source_start:split_idx].strip()
        if source.endswith(')'):
            source = source[:-1].strip()
        rhs_start = split_idx + 1
        depth = 0
        rhs_end = -1

        for idx in range(rhs_start, len(trans_str)):
            char = trans_str[idx]
            if char == '[':
                depth += 1
            elif char == ']':
                depth -= 1
                if depth == 0:
                    rhs_end = idx
                    break

        if rhs_end == -1:
            return source, []

        rhs_list_str = trans_str[rhs_start + 1:rhs_end]
        rhs_alternatives = self._parse_prolog_list(rhs_list_str)
        return source, rhs_alternatives
    
    def _parse_rhs_alternative(self, rhs: str) -> Tuple[List[str], List[str]]:
        """Parse RHS alternative: extract terminal and nonterminal symbols from one RHS alternative string.
        Returns: (terminals, nonterminals)
        """
        terminals = []
        nonterminals = []
        
        if not rhs or not isinstance(rhs, str):
            return terminals, nonterminals
        
        # Extract terminals from Prolog list structure [terminals, ...]
        if rhs.startswith('[') and rhs.endswith(']'):
            content = rhs[1:-1]
            terms = self._parse_prolog_list(content)
            for term in terms:
                text = term.strip()
                if text.startswith('(t(') and text.endswith(')'):
                    end_idx = text.rfind('),')
                    if end_idx != -1:
                        terminals.append(text[3:end_idx])
        
        # Extract nonterminals by scanning for (n(...)) patterns
        i = 0
        while i < len(rhs):
            if i < len(rhs) - 2 and rhs[i:i+3] == '(n(':
                start = i + 3
                paren_depth = 1
                j = start
                
                while j < len(rhs) and paren_depth > 0:
                    if rhs[j] == '(':
                        paren_depth += 1
                    elif rhs[j] == ')':
                        paren_depth -= 1
                    j += 1
                
                if paren_depth == 0:
                    nt_name = rhs[start:j-1]
                    if nt_name and nt_name not in nonterminals:
                        nonterminals.append(nt_name)
                    i = j
                else:
                    i += 1
            else:
                i += 1
        
        return terminals, nonterminals
    
    
    def _build_y_transition_mapping(self) -> Dict:
        """Build y_* to transition mapping in cg.pl generation order."""
        transition_info = {}
        y_idx = 1

        for trans_str in self.cfg_transitions:
            source, rhs_alternatives = self._parse_transition(trans_str)
            if not source:
                continue

            for rhs in rhs_alternatives:
                rhs_terminals, rhs_nonterminals = self._parse_rhs_alternative(rhs)
                transition_info[y_idx] = {
                    'source': source,
                    'rhs_terminals': rhs_terminals,
                    'rhs_nonterminals': rhs_nonterminals,
                }
                y_idx += 1

        # Build search indexes while we have the transition info
        for rule_num, info in transition_info.items():
            source = info.get('source', '')
            self.rules_by_source[source].append(rule_num)
            rhs_nonterminals = info.get('rhs_nonterminals', [])
            self.rule_rhs_nonterminals[rule_num] = rhs_nonterminals

        return transition_info
    
    def dump_cfg_to_file(self, output_file: str = "cfg_dump.txt") -> None:
        """Write the complete CFG (grammar rules) to a file in human-readable format."""
        with open(output_file, 'w') as f:
            f.write("=" * 80 + "\n")
            f.write("COMPLETE CONTEXT-FREE GRAMMAR\n")
            f.write("=" * 80 + "\n\n")
            
            f.write(f"Total Rules: {len(self.y_transition_info)}\n")
            f.write(f"Total Sources (Nonterminals): {len(self.rules_by_source)}\n\n")
            
            f.write("=" * 80 + "\n")
            f.write("RULE SUMMARY\n")
            f.write("=" * 80 + "\n\n")
            
            for rule_num in sorted(self.y_transition_info.keys()):
                info = self.y_transition_info[rule_num]
                source = info.get('source', '???')
                rhs_nts = info.get('rhs_nonterminals', [])
                rhs_terms = info.get('rhs_terminals', [])
                
                items = []
                if rhs_nts:
                    items.extend([f"<{nt}>" for nt in rhs_nts])
                if rhs_terms:
                    items.extend([f"'{term}'" for term in rhs_terms])
                
                rhs_str = " ".join(items) if items else "ε"
                f.write(f"y_{rule_num:3d}: {source:<50s} → {rhs_str}\n")
    
    
    # -------------------- TRACE RECONSTRUCTION ------------------------
    
    def find_derivation(self) -> Optional[List[Tuple[int, str, List[str]]]]:
        """
        Find a Grammar-Guided derivation order using a backtracking search.
        
        Returns: List of (rule_num, source, terminals) tuples, or None if no valid derivation
        """
        model_y_counts = {rule: count for rule, count in self.fired_rules}
        remaining_rules = dict(model_y_counts)
        execution_trace: List[Tuple[int, str, List[str]]] = []
        nonterminal_stack: List[str] = ['start']
        
        success = self._dfs_derivation_r(
            nonterminal_stack=nonterminal_stack,
            remaining_rules=remaining_rules,
            execution_trace=execution_trace
        )
        
        return execution_trace if success else None
    
    def _dfs_derivation_r(self, nonterminal_stack: List[str],
                                     remaining_rules: Dict[int, int],
                                     execution_trace: List) -> bool:
        """Recursive backtracking search for valid derivation."""
        
        if not nonterminal_stack and all(count == 0 for count in remaining_rules.values()):
            return True
        if not nonterminal_stack:
            return False
        current_nt = nonterminal_stack.pop(0)
        
        available_rules = [r for r in self.rules_by_source.get(current_nt, [])
                          if remaining_rules.get(r, 0) > 0]
        
        if not available_rules:
            nonterminal_stack.insert(0, current_nt)
            return False
        
        for rule_num in sorted(available_rules):
            info = self.y_transition_info[rule_num]
            source = info.get('source', '')
            terminals = info.get('rhs_terminals', [])
            rhs_nts = self.rule_rhs_nonterminals.get(rule_num, [])
            
            remaining_rules[rule_num] -= 1
            execution_trace.append((rule_num, source, terminals, rhs_nts))
            
            # The CFG encoding of call+continuation transitions is inconsistent:
            # sometimes the callee (_0_pd) comes first, sometimes the continuation
            # does. normalised by always putting the callee first so it gets
            # expanded (executed) before the continuation, matching source semantics.
            callees = [nt for nt in rhs_nts if _is_callee(nt)]
            continuations = [nt for nt in rhs_nts if not _is_callee(nt)]
            ordered_rhs = callees + continuations
            new_stack = ordered_rhs + nonterminal_stack
            
            if self._dfs_derivation_r(new_stack, remaining_rules, execution_trace):
                return True
            
            execution_trace.pop()
            remaining_rules[rule_num] += 1
        
        nonterminal_stack.insert(0, current_nt)
        return False
    
    # ==================== ANALYSIS HELPERS ====================
    
    def _extract_function_from_nonterminal(self, source_name: Optional[str]) -> Optional[str]:
        """Extract function name from nonterminal symbol"""
        if not source_name:
            return None

        # handles both simple names like v_leak_rec_0_pd0 and composite tuples
        matches = re.findall(r"v_([A-Za-z_]\w*)_(\d+)_pd\d+", source_name)
        if not matches:
            return None

        for func, _ in matches:
            if func.startswith("q") or func.startswith("sbot") or func.startswith("new"):
                continue
            return func

        return matches[0][0]
    
    # ------------------- OUTPUT & REPORTING ---------------------
    
    def write_decoded_trace_txt(self, output_path: str) -> bool:
        """
        Write a complete trace file with summary, derivation, and execution path in one file.
        """

        buffer = io.StringIO()
        with redirect_stdout(buffer):
            self.print_summary()
        summary_text = buffer.getvalue()
        

        derivation = self.find_derivation()
        
        if derivation is None:
            return False
        
        lines = []
        
        lines.append(summary_text.rstrip())
        lines.append("")

        lines.append("=" * 70)
        lines.append("DERIVATION ORDER")
        lines.append("=" * 70)
        lines.append("")
        
        for step, (rule_num, source, terminals, rhs_nts) in enumerate(derivation, 1):
            term_str = f" -> {terminals}" if terminals else ""
            lines.append(f"Step {step:2d}: Apply rule y_{rule_num:3d} - {source[:50]}{term_str}")
        
        lines.append("")
        lines.append("=" * 70)
        lines.append(f"Total steps: {len(derivation)}")
        lines.append("=" * 70)

        lines.append("")
        lines.append("")
        execution_summary = self.build_execution_summary_from_derivation()
        lines.append(execution_summary.rstrip())
        
        Path(output_path).write_text("\n".join(lines) + "\n")
        return True
    
    def print_summary(self):
        print("=" * 70)
        print("SMT MODEL TRACE SUMMARY (from CFG)")
        print("=" * 70)
        
        print(f"\n[CFG STRUCTURE]")
        print(f"  Nonterminals: {len(self.cfg_nonterminals)}")
        print(f"  Terminals: {len(self.cfg_terminals)}")
        print(f"  Transition Groups (tran): {len(self.cfg_transitions)}")
        print(f"  Transition Alternatives (y_*): {len(self.y_transition_info)}")
        
        print("\n[TERMINALS - Program Events]")
        if self.terminal_counts:
            for name, count in sorted(self.terminal_counts.items()):
                print(f"  {name:30} : {count:3} occurrence(s)")
        else:
            print("  No terminals fired")

        print("\n[PRODUCTION RULES FIRED (y_* > 0)]")
        if self.fired_rules:
            for rule_num, count in self.fired_rules:
                if rule_num in self.y_transition_info:
                    source = self.y_transition_info[rule_num].get('source', '')
                    transition_name = source if source else f"Rule_{rule_num}"
                else:
                    transition_name = self.nonterminals.get(rule_num, f"Rule_{rule_num}")
                print(f"  y_{rule_num:2} : {count:2} time(s) - {transition_name}")
        else:
            print("No rules fired")

        if self.cfg_transitions:
            print(f"\n[CFG TRANSITION GROUPS AVAILABLE: {len(self.cfg_transitions)}]")
            print(f"[CFG TRANSITION ALTERNATIVES AVAILABLE: {len(self.y_transition_info)}]")
        
        self._print_action_analysis(self.terminal_counts)
    
    def build_execution_summary_from_derivation(self) -> str:
        """
        Build user-facing execution summary from grammar-guided derivation.
        """
        derivation = self.find_derivation()
        if derivation is None:
            return "Could not derive execution order\n"

        lines = []
        lines.append("EXECUTION SUMMARY")
        lines.append("=" * 60)

        lines.append("\nCall path:")
        call_stack = []
        pc0_count = defaultdict(int)

        # Track pending stack of nonterminals to detect entries/exits
        pending_stack = ['start']
        prev_funcs_on_stack = set()

        for step, (rule_num, source, terminals, rhs_nts) in enumerate(derivation, 1):
            # Pop the current nonterminal being expanded
            if pending_stack and _extract_base_name(pending_stack[0]) == _extract_base_name(source):
                pending_stack.pop(0)

            # Push RHS nonterminals, callees first (same ordering as DFS)
            callees = [nt for nt in rhs_nts if _is_callee(nt)]
            continuations = [nt for nt in rhs_nts if not _is_callee(nt)]
            ordered_rhs = callees + continuations
            pending_stack = ordered_rhs + pending_stack

            # Extract all functions currently on the stack
            current_funcs_on_stack = defaultdict(list)
            for nt in pending_stack:
                nt_func = self._extract_function_from_nonterminal(nt)
                if nt_func:
                    pc_match = re.search(r'_(\d+)_pd', nt)
                    pc = int(pc_match.group(1)) if pc_match else None
                    if pc is not None:
                        current_funcs_on_stack[nt_func].append((pc, nt))

            current_funcs = set(current_funcs_on_stack.keys())

            # Detect entries: functions that just appeared on the stack at PC=0
            for func in current_funcs - prev_funcs_on_stack:
                pcs = [pc for pc, nt in current_funcs_on_stack[func]]
                if 0 in pcs:
                    pc0_count[func] += 1
                    indent = "  " * len(call_stack)
                    lines.append(f"{indent}-> {func}() [call #{pc0_count[func]}]")
                    call_stack.append((func, pc0_count[func]))

            # Detect exits: functions that left the stack
            for func in prev_funcs_on_stack - current_funcs:
                while call_stack and call_stack[-1][0] != func:
                    popped = call_stack.pop()
                    indent = "  " * len(call_stack)
                    lines.append(f"{indent}<- {popped[0]}() [return from call #{popped[1]}]")
                if call_stack and call_stack[-1][0] == func:
                    popped = call_stack.pop()
                    indent = "  " * len(call_stack)
                    lines.append(f"{indent}<- {popped[0]}() [return from call #{popped[1]}]")

            prev_funcs_on_stack = current_funcs

        # Key events
        lines.append("")
        lines.append("Key events (in execution order):")

        event_count = 1
        found_events = False

        for step, (rule_num, source, terminals, rhs_nts) in enumerate(derivation, 1):
            for terminal in terminals:
                term_lower = terminal.lower()

                for echo_name in self.action_echos:
                    if echo_name.lower() in term_lower:
                        func = self._extract_function_from_nonterminal(source)
                        func_str = f"{func}()" if func else "unknown"
                        lines.append(f"  {event_count}. Step {step}: {echo_name} at {func_str}")
                        event_count += 1
                        found_events = True
                        break

                if 'done' in term_lower:
                    func = self._extract_function_from_nonterminal(source)
                    func_str = f"{func}()" if func else "unknown"
                    lines.append(f"  {event_count}. Step {step}: done at {func_str}")
                    event_count += 1
                    found_events = True

        if not found_events:
            lines.append("no events found")

        return "\n".join(lines) + "\n"

    def _print_action_analysis(self, terminal_counts: Dict[str, int]):
        """Display configured tracked actions"""
        print("\n" + "=" * 70)
        print("ACTION ANALYSIS")
        print("=" * 70)
        
        action_counts = {}
        for echo_name in self.action_echos:
            var_name = f'v_{echo_name}_pd0'
            action_counts[echo_name] = terminal_counts.get(var_name, 0)
        
        done_count = terminal_counts.get('v_done_pd0', 0)
        
        print(f"\nTracked Operations:")
        for echo_name, count in action_counts.items():
            print(f"  {echo_name.capitalize():20s}: {count}")
        print(f"  Program done signal:     {done_count}")


def main():
    parser = argparse.ArgumentParser(description="Decode SMT model trace into human-readable execution")
    parser.add_argument("--model", required=True, help="Path to solver model file")
    parser.add_argument("--debug", required=True, help="Path to debugging.txt")
    parser.add_argument("--cfg", required=True, help="Path to debugging2.txt")
    parser.add_argument("--source-c", default=None, help="Optional path to source C file for line references")
    parser.add_argument("--decoded-trace-out", default=None, help="Optional path to write grammar-guided derivation order")
    parser.add_argument("--tracked-actions", default=None, help="JSON dict of tracked actions (action_name -> {functions: [...], echo: ...})")
    args = parser.parse_args()

    tracked_actions = None
    if args.tracked_actions:
        import json
        try:
            tracked_actions_dict = json.loads(args.tracked_actions)
            for action_name, action_config in tracked_actions_dict.items():
                action_config["functions"] = set(action_config.get("functions", []))
            tracked_actions = tracked_actions_dict
        except json.JSONDecodeError:
            print(f"Warning: Could not parse --tracked-actions JSON: {args.tracked_actions}")
    
    decoder = TraceDecoder(
        args.model, 
        args.debug, 
        args.cfg,
        args.source_c,
        tracked_actions=tracked_actions,
    )

    if args.decoded_trace_out:
        import os
        output_dir = os.path.dirname(args.decoded_trace_out)
        if not output_dir:
            output_dir = "."
        cfg_out = os.path.join(output_dir, "cfg_dump.txt")
        decoder.dump_cfg_to_file(cfg_out)
        print(f"Wrote grammar dump: {cfg_out}")

    if args.decoded_trace_out:
        if decoder.write_decoded_trace_txt(args.decoded_trace_out):
            print(f"Wrote complete decoded trace: {args.decoded_trace_out}")

    decoder.print_summary()


if __name__ == "__main__":
    main()
