#!/usr/bin/env python3
"""Run the full local pipeline from C source to decoded trace artifacts.

Stages:
1) C -> .prog
2) .prog -> Prolog module
3) Prolog module -> SMT instance
4) Solve SMT with Yices -> model.txt
5) Decode model with trace_decoder
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import shutil
import subprocess
import sys


from pathlib import Path


#
# Each action maps to a dict with:
#   "functions": set of function names to match
#   "echo": what to echo when matched
#
# EDIT TRACKED_ACTIONS here to add custom actions, or modify existing ones.
TRACKED_ACTIONS: dict[str, dict] = {
    "malloc": {
        "functions": {
            "malloc"
        },
        "echo": "malloc"
    },
    "free": {
        "functions": {
            "free"
        },
        "echo": "free"
    }
}

# EDIT DEFAULT_CONSTRAINTS here to change pipeline defaults.
DEFAULT_CONSTRAINTS: dict = {
    "constraints": ["malloc != free"],  
    "max_reversals": 0,                
}


def _run(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
	result = subprocess.run(
		cmd,
		cwd=str(cwd) if cwd else None,
		stdout=subprocess.PIPE,
		stderr=subprocess.PIPE,
		text=True,
	)
	if result.returncode != 0:
		joined = " ".join(cmd)
		raise RuntimeError(
			f"Command failed ({result.returncode}): {joined}\n"
			f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
		)
	return result


def _run_shell(command: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
	"""Run a command in a login shell (useful for environment modules)."""
	result = subprocess.run(
		["bash", "-lc", command],
		cwd=str(cwd) if cwd else None,
		stdout=subprocess.PIPE,
		stderr=subprocess.PIPE,
		text=True,
	)
	if result.returncode != 0:
		raise RuntimeError(
			f"Shell command failed ({result.returncode}): {command}\n"
			f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
		)
	return result


def _find_pushdown_binary(project_root: Path) -> Path:
	# Local build often has this exact (misspelled) name.
	candidates = [
		project_root / "pushdownTranslator" / "bin" / "main" / "pushdown_translater",
		project_root / "pushdownTranslator" / "bin" / "main" / "pushdown_translator",
	]
	for candidate in candidates:
		if candidate.exists() and candidate.is_file():
			return candidate

	# Fallback to PATH if user has installed it globally.
	for name in ("pushdown_translater", "pushdown_translator"):
		found = shutil.which(name)
		if found:
			return Path(found)

	searched = "\n".join(str(c) for c in candidates)
	raise FileNotFoundError(
		"Could not find pushdown translator binary. Searched:\n"
		f"{searched}\n"
		"Also looked in PATH for pushdown_translater/pushdown_translator."
	)


def _find_swipl(explicit: str | None = None) -> str:
	if explicit:
		candidate = Path(explicit)
		if candidate.exists() and candidate.is_file():
			return str(candidate.resolve())
		found = shutil.which(explicit)
		if found:
			return found
		raise FileNotFoundError(
			f"Could not resolve SWI-Prolog binary from --swipl-bin={explicit}"
		)

	found = shutil.which("swipl")
	if found:
		return found
	raise FileNotFoundError(
		"Could not find 'swipl' in PATH. Load/install SWI-Prolog first, or pass --swipl-bin."
	)


def _find_yices(project_root: Path, explicit: str | None = None) -> str:
	if explicit:
		candidate = Path(explicit)
		if candidate.exists() and candidate.is_file():
			return str(candidate.resolve())
		found = shutil.which(explicit)
		if found:
			return found
		raise FileNotFoundError(
			f"Could not resolve Yices binary from --yices-bin={explicit}"
		)
	# Check several project-local locations for a bundled Yices binary
	candidates = [
		project_root / "ogSolver" / "yices" / "bin" / "yices-smt2",
		project_root / "yices" / "bin" / "yices-smt2",
		project_root / "yices" / "yices-smt2",
	]
	for local in candidates:
		if local.exists() and local.is_file():
			return str(local.resolve())

	# Fallback to PATH
	found = shutil.which("yices-smt2")
	if found:
		return found

	searched = "\n".join(str(c) for c in candidates)
	raise FileNotFoundError(
		"Could not find yices-smt2. Searched project locations:\n"
		f"{searched}\nAlso checked PATH for 'yices-smt2'."
	)


def _extract_solver_status(model_output: str) -> str:
	"""Extract top-level SMT result from solver output."""
	for raw in model_output.splitlines():
		line = raw.strip().lower()
		if line in {"sat", "unsat", "unknown"}:
			return line
	return "unrecognized"


def main() -> None:
	parser = argparse.ArgumentParser(
		description="Generate pipeline artifacts from a C file or .prog file (.prog skips C translation stage)"
	)
	parser.add_argument("input_file", help="Path to input C file or .prog file")
	parser.add_argument(
		"--project-root",
		default=str(Path(__file__).resolve().parent),
		help="Project root directory (default: directory containing this script)",
	)
	parser.add_argument(
		"--work-dir",
		default=None,
		help=(
			"Output directory for generated artifacts. "
			"Default: <modelChecker_dir>/<input_stem>_intermediary_files"
		),
	)
	parser.add_argument(
		"--entry",
		default=None,
		help="Optional entry function for c_to_prog.py (default: auto/main)",
	)
	parser.add_argument(
		"--alloc",
		default=None,
		help="Extra allocator names, comma-separated",
	)
	parser.add_argument(
		"--free",
		default=None,
		help="Extra deallocator names, comma-separated",
	)
	parser.add_argument(
		"--clang-args",
		default="",
		help='Extra clang flags for c_to_prog.py, e.g. "-I/some/include"',
	)
	parser.add_argument(
		"--dump-ast",
		action="store_true",
		help="Forward --dump-ast to c_to_prog.py to write an AST dump alongside output",
	)
	parser.add_argument(
		"--constraints",
		default=None,
		help=(
			"Constraint strings comma-separated (e.g., 'malloc != free,malloc > free'). "
			"Defaults to config in modelChecker.py"
		),
	)
	parser.add_argument(
		"--prolog-name",
		default=None,
		help="Output Prolog filename (default: <c_stem>.pl)",
	)
	parser.add_argument(
		"--prolog-goal",
		default="gencall",
		help="Prolog goal to generate SMT instance (default: gencall)",
	)
	parser.add_argument(
		"--smt-name",
		default=None,
		help="Output SMT filename (default: <c_stem>.smt2)",
	)
	parser.add_argument(
		"--swipl-bin",
		default=None,
		help="Path or command name for SWI-Prolog executable (default: swipl from PATH)",
	)
	parser.add_argument(
		"--swipl-module",
		default="cs262-swipl",
		help=(
			"Environment module to load before SWI-Prolog stage "
			"(default: cs262-swipl, set to 'none' to disable)"
		),
	)
	parser.add_argument(
		"--yices-bin",
		default=None,
		help="Path or command name for yices-smt2 (default: ogSolver/yices/bin/yices-smt2 or PATH)",
	)
	parser.add_argument(
		"--disable-pushpop",
		action="store_true",
		help="Disable the 'pushpop' PDS optimiser in the pushdown translator (prevents inlining/removal of calls)",
	)
	parser.add_argument(
		"--pdsopts",
		default=None,
		help=(
			"Comma-separated list of PDS optimisers to run in the pushdown translator. "
			"If omitted, the translator defaults are used. Use 'none' to disable all."
		),
	)
	parser.add_argument(
		"--progopts",
		default=None,
		help=(
			"Comma-separated list of program (source) optimisers to run in the pushdown translator. "
			"If omitted, defaults to 'none' (no source-level optimisations)."
		),
	)
	parser.add_argument(
		"--trace-decoder",
		default=None,
		help="Path to trace_decoder.py (default: <project_root>/ogSolver/trace_decoder.py)",
	)
	parser.add_argument(
		"--debug-file",
		default=None,
		help=(
			"Path to debugging.txt. "
			"Default: <work_dir>/debugging.txt if generated, otherwise <project_root>/prologToSMT/debugging.txt"
		),
	)
	parser.add_argument(
		"--cfg-file",
		default=None,
		help=(
			"Path to debugging2.txt. "
			"Default: <work_dir>/debugging2.txt if generated, otherwise <project_root>/prologToSMT/debugging2.txt"
		),
	)
	parser.add_argument(
		"--model-name",
		default="model.txt",
		help="Output model filename from Yices (default: model.txt)",
	)
	parser.add_argument(
		"--trace-text-name",
		default="decoded_trace.txt",
		help="Filename for human-readable decoded trace output",
	)

	args = parser.parse_args()

	script_dir = Path(__file__).resolve().parent
	project_root = Path(args.project_root).resolve()

	# If user provided a relative/simple input name, try to resolve it under
	# common locations inside the project tree (c_files/). This helps when
	# the repo has been reorganised and the caller expects inputs in `c_files`.
	input_file = Path(args.input_file)
	if not input_file.is_absolute():
		candidates = [
			script_dir / args.input_file,
			script_dir / 'c_files' / args.input_file,
			project_root / args.input_file,
			project_root / 'c_files' / args.input_file,
			script_dir.parent / args.input_file,
		]
		found = None
		for c in candidates:
			if c.exists():
				found = c.resolve()
				break
		if found:
			input_file = found
		else:
			input_file = Path(args.input_file).resolve()

	if not input_file.exists():
		raise SystemExit(f"Input file not found: {input_file}")

	# Determine input type and which pipeline stage to start from.
	suffix = input_file.suffix.lower()
	is_c_file = suffix == ".c"
	is_prog_file = suffix == ".prog"
	is_pl_file = suffix == ".pl"
	is_smt_file = suffix in {".smt2", ".smt"}
	is_model_file = input_file.name == args.model_name or input_file.suffix.lower() == ".txt"

	if not (is_c_file or is_prog_file or is_pl_file or is_smt_file or is_model_file):
		raise SystemExit(f"Input file must be one of .c, .prog, .pl, .smt2, or model.txt; got: {input_file}")

	# Locate the translator script in several plausible locations inside the
	# project folder (handles reorganised repo layouts). Prefer a local
	# pushdownTranslator copy, then fallback to top-level c_to_prog.py.
	c_to_prog_candidates = [
		project_root / "pushdownTranslator" / "c_to_prog.py",
		project_root / "c_to_prog.py",
		script_dir / "c_to_prog.py",
		script_dir.parent / "c_to_prog.py",
		project_root / "project" / "c_to_prog.py",
	]
	c_to_prog = None
	if is_c_file:
		for cand in c_to_prog_candidates:
			if cand.exists():
				c_to_prog = cand.resolve()
				break
		if c_to_prog is None:
			raise SystemExit(f"Missing translator script; tried: {c_to_prog_candidates}")

	pushdown_bin = _find_pushdown_binary(project_root)
	module_enabled = str(args.swipl_module).lower() != "none"
	if module_enabled and args.swipl_bin is None:
		# Resolve after module load in a login shell.
		swipl_bin = "swipl"
	else:
		swipl_bin = _find_swipl(args.swipl_bin)
	call_pl = project_root / "prologToSMT" / "call.pl"
	if not call_pl.exists():
		raise SystemExit(f"Missing Prolog wrapper: {call_pl}")

	yices_bin = _find_yices(project_root, args.yices_bin)

	# Locate trace_decoder in likely places (project-local copy or ogSolver/)
	if args.trace_decoder:
		trace_decoder = Path(args.trace_decoder).resolve()
	else:
		td_candidates = [
			project_root / "trace_decoder.py",
			project_root / "ogSolver" / "trace_decoder.py",
			script_dir / "trace_decoder.py",
			script_dir.parent / "trace_decoder.py",
		]
		trace_decoder = None
		for tdc in td_candidates:
			if tdc.exists():
				trace_decoder = tdc.resolve()
				break
	if trace_decoder is None or not trace_decoder.exists():
		raise SystemExit(f"Missing trace decoder; looked in: {td_candidates}")

	if args.work_dir:
		work_dir_candidate = Path(args.work_dir)
		if work_dir_candidate.is_absolute():
			work_dir = work_dir_candidate
		else:
			# Relative paths are resolved next to modelChecker.py.
			work_dir = script_dir / work_dir_candidate
	else:
		# Place per-run artifacts under a centralized `output/` directory
		work_dir = script_dir / "output" / f"{input_file.stem}_output"

	work_dir = work_dir.resolve()
	work_dir.mkdir(parents=True, exist_ok=True)

	# Resolve per-stage input/output paths depending on starting stage
	if is_c_file:
		prog_path = work_dir / f"{input_file.stem}.prog"
	elif is_prog_file:
		prog_path = input_file
	else:
		prog_path = work_dir / f"{input_file.stem}.prog"
	prolog_name = args.prolog_name or f"{input_file.stem}.pl"
	prolog_path = work_dir / prolog_name
	smt_name = args.smt_name or f"{input_file.stem}.smt2"
	smt_path = work_dir / smt_name
	model_path = work_dir / args.model_name
	trace_text_path = work_dir / args.trace_text_name


	# Stage 1: C -> .prog (only when input is .c)
	if is_c_file:
		cmd_prog = [
			sys.executable,
			str(c_to_prog),
			str(input_file),
			"--output",
			str(prog_path),
		]
		if args.entry:
			cmd_prog += ["--entry", args.entry]
		if args.alloc:
			cmd_prog += ["--alloc", args.alloc]
		if args.free:
			cmd_prog += ["--free", args.free]
		if args.clang_args:
			cmd_prog += ["--clang-args", args.clang_args]
		if args.constraints:
			cmd_prog += ["--constraints", args.constraints]
		# Forward AST dump request to the translator if requested
		if getattr(args, 'dump_ast', False):
			cmd_prog += ["--dump-ast"]

		_run(cmd_prog, cwd=project_root)
	elif is_prog_file:
		# already have .prog; nothing to do
		pass
	elif is_pl_file:
		# user started from .pl; skip to Stage 3
		pass
	elif is_smt_file or is_model_file:
		pass

	# Stage 2: .prog -> Prolog (module with gencall/gencall_alt)
	pushdown_cmd = [str(pushdown_bin), str(prog_path)]
	if args.progopts is not None:
		pushdown_cmd += ["--progopts", args.progopts]
	else:
		pushdown_cmd += ["--progopts", "none"]

	if args.pdsopts is not None:
		pushdown_cmd += ["--pdsopts", args.pdsopts]
	elif args.disable_pushpop:
		pushdown_cmd += ["--pdsopts", "compress,silentloop"]
	else:
		pushdown_cmd += ["--pdsopts", "none"]

	result_prolog = _run(pushdown_cmd, cwd=project_root)
	prolog_path.write_text(result_prolog.stdout)

	# Stage 3: Prolog -> SMT instance (via prologToSMT/call.pl + generated module)
	generated_txt = work_dir / "output.txt"
	work_debug_file = work_dir / "debugging.txt"
	work_cfg_file = work_dir / "debugging2.txt"
	if generated_txt.exists():
		generated_txt.unlink()
	# Remove stale per-run debug artifacts so decode uses fresh metadata from this run.
	if work_debug_file.exists():
		work_debug_file.unlink()
	if work_cfg_file.exists():
		work_cfg_file.unlink()

	goal = f"{args.prolog_goal},halt."
	swipl_cmd = [
		swipl_bin,
		"-q",
		"-s",
		str(call_pl),
		"-s",
		str(prolog_path),
		"-g",
		goal,
	]

	if module_enabled:
		shell_cmd = f"module load {shlex.quote(args.swipl_module)} && " + " ".join(
			shlex.quote(part) for part in swipl_cmd
		)
		_run_shell(shell_cmd, cwd=work_dir)
	else:
		_run(swipl_cmd, cwd=work_dir)

	if not generated_txt.exists():
		raise RuntimeError(
			"Prolog stage completed but did not produce output.txt in work directory."
		)

	if smt_path.exists():
		smt_path.unlink()
	generated_txt.rename(smt_path)

	# Stage 4: SMT -> model.txt (Yices)
	result_model = _run([yices_bin, str(smt_path)], cwd=work_dir)
	model_path.write_text(result_model.stdout)
	solver_status = _extract_solver_status(result_model.stdout)

	if args.debug_file:
		debug_file = Path(args.debug_file).resolve()
	elif work_debug_file.exists():
		debug_file = work_debug_file.resolve()
	else:
		debug_file = (project_root / "prologToSMT" / "debugging.txt").resolve()

	if args.cfg_file:
		cfg_file = Path(args.cfg_file).resolve()
	elif work_cfg_file.exists():
		cfg_file = work_cfg_file.resolve()
	else:
		cfg_file = (project_root / "prologToSMT" / "debugging2.txt").resolve()

	if not debug_file.exists():
		raise SystemExit(f"Missing debug file: {debug_file}")
	if not cfg_file.exists():
		raise SystemExit(f"Missing CFG debug file: {cfg_file}")

	# Build tracked_actions for trace_decoder (same logic as c_to_prog.py)
	# Convert to JSON-compatible format (sets -> lists)
	tracked_actions_for_trace = {}
	for action_name, config in TRACKED_ACTIONS.items():
		user_actions = {}
		if action_name == "malloc" and args.alloc:
			user_actions["malloc"] = set(args.alloc.split(","))
		elif action_name == "free" and args.free:
			user_actions["free"] = set(args.free.split(","))
		
		tracked_actions_for_trace[action_name] = {
			"functions": sorted(list(config["functions"] | user_actions.get(action_name, set()))),
			"echo": config["echo"]
		}
	
	# Stage 5: Decode model using debug files and source mapping
	decode_cmd = [
		sys.executable,
		str(trace_decoder),
		"--model",
		str(model_path),
		"--debug",
		str(debug_file),
		"--cfg",
		str(cfg_file),
		"--source-c",
		str(input_file),
		"--tracked-actions",
		json.dumps(tracked_actions_for_trace),
		"--decoded-trace-out",
		str(trace_text_path),
	]
	_run(decode_cmd, cwd=work_dir)

	print("Pipeline stage complete.")
	print(f"Input file:    {input_file}")
	if is_c_file:
		print(f"Generated .prog: {prog_path}")
	print(f"Generated .pl:   {prolog_path}")
	print(f"Generated .smt2: {smt_path}")
	print(f"Generated model: {model_path}")
	print(f"SMT result:      {solver_status}")
	print(f"Decoded trace:   {trace_text_path}")


	if solver_status == "sat":
		block_count = 0

		base_smt_text = smt_path.read_text()
		low_base = base_smt_text.lower()
		check_idx = low_base.rfind("(check-sat")
		if check_idx == -1:
			check_idx = len(base_smt_text)
		accum_blocks: list[str] = []
		while True:
			# Extract and display execution summary from decoded trace
			if trace_text_path.exists():
				content = trace_text_path.read_text()
				if "EXECUTION SUMMARY" in content:
					exec_start = content.find("EXECUTION SUMMARY")
					print(content[exec_start:])

			resp = input("Accept this witness? [(a)ccept/(c)ontinue/(q)uit]: ").strip().lower()
			if resp in {"a", "accept"}:
				print("Witness accepted by user.")
				break
			if resp in {"q", "quit", "exit"}:
				print("Exiting without accepting witness.")
				sys.exit(0)
			if resp not in {"c", "continue", "n", "next"}:
				print("Unrecognized choice; please enter 'a', 'c', or 'q'.")
				continue


			model_text = model_path.read_text()
			# Match define-fun lines like: (define-fun z_n_13 () Int 7)
			define_re = re.compile(r"\(define-fun\s+([^\s]+)\s*\(\)\s+[^\s]+\s+([^\)]+)\)")
			assignments: list[str] = []
			for m in define_re.finditer(model_text):
				name = m.group(1)
				value = m.group(2).strip()
				# Skip uninterpretable values
				if not name or not value:
					continue
				assignments.append(f"(= {name} {value})")

			if not assignments:
				print("Could not extract model assignments to block; aborting continue.")
				break

			conj = "(and " + " ".join(assignments) + ")"
			block_assert = f"\n; Blocking previous model (attempt {block_count + 1})\n(assert (not {conj}))\n"


			accum_blocks.append(block_assert)
			new_smt_text = base_smt_text[:check_idx] + "\n".join(accum_blocks) + "\n" + base_smt_text[check_idx:]
			# Overwrite the original SMT so subsequent runs use the accumulated blocks.
			smt_path.write_text(new_smt_text)

			print(f"Running solver on updated SMT (attempt {block_count + 1}) -> {smt_path}")
			result_model = _run([yices_bin, str(smt_path)], cwd=work_dir)
			model_path.write_text(result_model.stdout)
			solver_status = _extract_solver_status(result_model.stdout)


			_run(decode_cmd, cwd=work_dir)

			print(f"SMT result: {solver_status}")
			block_count += 1

			if solver_status != "sat":
				print("Solver returned non-SAT after blocking; stopping search.")
				break


if __name__ == "__main__":
	main()