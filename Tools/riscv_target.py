"""The RISC-V target of VeIR's driver scripts, so that clang, llc and QEMU agree.

We target riscv64 Linux: the hard-float ABI, which is the one that the riscv64
C libraries use, on rv64gc, plus every extension that VeIR's instruction
selector can emit (see MIRPrinter.lean).
"""

from __future__ import annotations

import re

TRIPLE = "riscv64-unknown-linux-gnu"
ABI = "lp64d"
VEIR_EXTENSIONS = ("zba", "zbb", "zbs", "zbc", "zbkb", "zicond")
MARCH = "rv64gc_" + "_".join(VEIR_EXTENSIONS)
# llc has no feature for G. F implies Zicsr; nothing we generate needs Zifencei.
FEATURES = ",".join(f"+{ext}" for ext in ("m", "a", "f", "d", "c", *VEIR_EXTENSIONS))

CLANG_TARGET_FLAGS = (f"--target={TRIPLE}", f"-march={MARCH}", f"-mabi={ABI}")
LLC_TARGET_FLAGS = (f"-mtriple={TRIPLE}", f"-mattr={FEATURES}", f"-target-abi={ABI}")
# QEMU's rv64 CPU already has everything in rv64gc.
QEMU_CPU = "rv64," + ",".join(f"{ext}=true" for ext in VEIR_EXTENSIONS)
# The Lima VM that runs QEMU on macOS, where qemu-riscv64 doesn't exist.
RISCV_VM = "rv64"
# Runs the ELF read from stdin, so that the VM needn't see the file; $1 is the -cpu
# spec, $2 the timeout in seconds.
QEMU_RUNNER = ('f=$(mktemp) && cat >"$f" && chmod +x "$f" && '
               'timeout "$2" qemu-riscv64 -cpu "$1" "$f"; rc=$?; rm -f "$f"; exit $rc')


def retarget_mir(mir: str) -> str:
    """Function attributes override llc's -mattr, and the standalone MIR printer
    uses an integer-only target, so give `mir` the features of the full target."""
    return re.sub(r'"target-features"="[^"]*"', f'"target-features"="{FEATURES}"', mir)
