#!/usr/bin/env python3
"""This program converts an LLVM IR file into MLIR in the LLVM
dialect, optimizes it using either a predefined or a user-specified
VeIR optimization pipeline, converts the optimized MLIR back into
LLVM, and finally invokes alive-tv to check whether the entire process
has resulted in a refinement of the original file.
"""

import argparse
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("input", help="Input LLVM IR file (.ll or .bc)")
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
        with open(opt_mlir, "w") as f:
            r = subprocess.run(
                ["lake", "exec", "veir-opt", f"-p={args.passes}", str(src_mlir)],
                cwd=PROJECT_ROOT, stdout=f,
            )
        if r.returncode != 0:
            sys.exit(r.returncode)

        # 3. MLIR -> LLVM IR.
        with open(tgt_ll, "w") as f:
            r = subprocess.run(
                ["mlir-translate", "--mlir-to-llvmir", str(opt_mlir)],
                stdout=f,
            )
        if r.returncode != 0:
            sys.exit(r.returncode)

        # 4. Refinement check.
        alive_cmd = shlex.join([
            "alive-tv", "--disable-undef-input", str(input_path), str(tgt_ll)
        ])
        print(f"$ {alive_cmd}", file=sys.stderr)
        r = subprocess.run(alive_cmd, shell=True)
        return r.returncode
    finally:
        shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
