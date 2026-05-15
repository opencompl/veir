#!/usr/bin/env python3
"""Verify that Veir's instcombine and dce passes refine an LLVM IR module.

Pipeline:
  input.ll
    --(mlir-translate --import-llvm | mlir-opt --mlir-print-op-generic
       --mlir-print-local-scope)--> src.mlir
    --(lake exec veir-opt -p=instcombine,dce)--> opt.mlir
    --(restore stripped llvm.func attributes)--> opt-patched.mlir
    --(mlir-translate --mlir-to-llvmir)-->       tgt.ll
    --(alive-tv input.ll tgt.ll)

veir-opt drops the `<{...}>` properties block from `llvm.func` operations on
output, including `sym_name` and `function_type`, which are required by
`mlir-translate --mlir-to-llvmir`. This script restores those properties from
the source MLIR before round-tripping back to LLVM IR.
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent


def run(cmd, **kwargs):
    """Run a command, echo it, fail loudly on nonzero exit."""
    print("$ " + " ".join(str(c) for c in cmd), file=sys.stderr)
    result = subprocess.run(cmd, **kwargs)
    if result.returncode != 0:
        sys.exit(result.returncode)
    return result


def find_props_end(text, start):
    """Given text[start:start+2] == '<{', return index just past matching '}>'."""
    i = start + 2
    depth = 1
    while i < len(text) and depth > 0:
        c = text[i]
        if c == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
        elif c == '{':
            depth += 1
            i += 1
        elif c == '}':
            depth -= 1
            i += 1
        else:
            i += 1
    if i < len(text) and text[i] == '>':
        return i + 1
    raise ValueError("unterminated <{...}> block")


def extract_func_props(text):
    """Return the `<{...}>` substring (or None) for each `llvm.func` in order."""
    needle = '"llvm.func"()'
    out = []
    i = 0
    while True:
        idx = text.find(needle, i)
        if idx < 0:
            return out
        i = idx + len(needle)
        j = i
        while j < len(text) and text[j].isspace():
            j += 1
        if j + 1 < len(text) and text[j:j+2] == '<{':
            end = find_props_end(text, j)
            out.append(text[j:end])
            i = end
        else:
            out.append(None)


def patch_func_props(opt_text, props_list):
    """Inject each saved `<{...}>` block into the matching `llvm.func` of opt_text."""
    needle = '"llvm.func"()'
    parts = []
    i = 0
    n = 0
    while True:
        idx = opt_text.find(needle, i)
        if idx < 0:
            parts.append(opt_text[i:])
            break
        parts.append(opt_text[i:idx + len(needle)])
        i = idx + len(needle)
        if n >= len(props_list):
            raise ValueError(
                f"veir-opt output has more llvm.func ops ({n + 1}) "
                f"than the source MLIR ({len(props_list)})"
            )
        if props_list[n] is not None:
            parts.append(" " + props_list[n])
        n += 1
    if n != len(props_list):
        raise ValueError(
            f"llvm.func count mismatch: source has {len(props_list)}, "
            f"veir-opt output has {n}"
        )
    return "".join(parts)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("input", help="Input LLVM IR file (.ll or .bc)")
    ap.add_argument("--keep", action="store_true",
                    help="Keep intermediate files (print their paths)")
    ap.add_argument("--passes", default="instcombine,dce",
                    help="Veir pass pipeline (default: instcombine,dce)")
    args = ap.parse_args()

    for tool in ("mlir-translate", "mlir-opt", "alive-tv", "lake"):
        if shutil.which(tool) is None:
            sys.exit(f"error: required tool not found in PATH: {tool}")

    input_path = Path(args.input).resolve()
    if not input_path.exists():
        sys.exit(f"error: input not found: {input_path}")

    workdir = Path(tempfile.mkdtemp(prefix="veir-check-"))
    try:
        src_mlir = workdir / "src.mlir"
        opt_mlir_raw = workdir / "opt-raw.mlir"
        opt_mlir = workdir / "opt.mlir"
        tgt_ll = workdir / "tgt.ll"

        # 1. LLVM IR -> generic MLIR.
        with open(src_mlir, "w") as f:
            translate = subprocess.Popen(
                ["mlir-translate", "--import-llvm", str(input_path)],
                stdout=subprocess.PIPE,
            )
            mlir_opt = subprocess.Popen(
                ["mlir-opt", "--mlir-print-op-generic", "--mlir-print-local-scope"],
                stdin=translate.stdout,
                stdout=f,
            )
            translate.stdout.close()
            mlir_opt.wait()
            translate.wait()
            if translate.returncode != 0 or mlir_opt.returncode != 0:
                sys.exit("error: failed to convert LLVM IR to MLIR")

        # 2. Run veir-opt from the project root (needed by lake).
        print(f"$ (cd {PROJECT_ROOT}) lake exec veir-opt -p={args.passes} {src_mlir}",
              file=sys.stderr)
        with open(opt_mlir_raw, "w") as f:
            r = subprocess.run(
                ["lake", "exec", "veir-opt", f"-p={args.passes}", str(src_mlir)],
                cwd=PROJECT_ROOT, stdout=f,
            )
        if r.returncode != 0:
            sys.exit(r.returncode)

        # 3. Restore llvm.func properties stripped by veir-opt.
        src_text = src_mlir.read_text()
        opt_text = opt_mlir_raw.read_text()
        props = extract_func_props(src_text)
        patched = patch_func_props(opt_text, props)
        opt_mlir.write_text(patched)

        # 4. MLIR -> LLVM IR.
        with open(tgt_ll, "w") as f:
            r = subprocess.run(
                ["mlir-translate", "--mlir-to-llvmir", str(opt_mlir)],
                stdout=f,
            )
        if r.returncode != 0:
            sys.exit(r.returncode)

        # 5. Refinement check.
        print(f"$ alive-tv --disable-undef-input {input_path} {tgt_ll}", file=sys.stderr)
        r = subprocess.run(["alive-tv", str(input_path), str(tgt_ll)])
        if args.keep:
            print(f"intermediate files kept in: {workdir}", file=sys.stderr)
        return r.returncode
    finally:
        if not args.keep:
            shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
