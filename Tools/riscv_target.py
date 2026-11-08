"""RISC-V Linux target shared by the compiler drivers and QEMU.

Keep the triple, ABI and features in sync with Veir/MIRPrinter.lean, which
emits them directly into standalone MIR along with the lp64d call masks.
"""

from __future__ import annotations

import re

TRIPLE = "riscv64-unknown-linux-gnu"
ABI = "lp64d"
VEIR_EXTENSIONS = ("zba", "zbb", "zbs", "zbc", "zbkb", "zicond")
MARCH = "rv64g_" + "_".join(VEIR_EXTENSIONS)
# Expand G for llc, which accepts individual features rather than -march.
# Keep compression off in both the driver and per-function MIR features:
# mixed 16/32-bit instructions incur extra fetches on gem5's TimingSimpleCPU.
FEATURES = ",".join(f"+{ext}" for ext in
                    ("m", "a", "f", "d", "zicsr", "zifencei", *VEIR_EXTENSIONS)) + ",-c"
CLANG_TARGET_FLAGS = (f"--target={TRIPLE}", f"-march={MARCH}", f"-mabi={ABI}")
LLC_TARGET_FLAGS = (f"-mtriple={TRIPLE}", f"-mattr={FEATURES}", f"-target-abi={ABI}")
# QEMU's rv64 CPU enables C by default; disable it so compressed instructions trap.
QEMU_CPU = "rv64,c=false," + ",".join(f"{ext}=true" for ext in VEIR_EXTENSIONS)

# Programs linked against system libraries must allow their compressed code.
QEMU_LIBC_CPU = "rv64," + ",".join(f"{ext}=true" for ext in VEIR_EXTENSIONS)
# The Lima VM that runs QEMU on macOS, where qemu-riscv64 doesn't exist.
RISCV_VM = "rv64"
# Runs the ELF read from stdin, so that the VM needn't see the file; $1 is the -cpu
# spec, $2 the timeout in seconds.
QEMU_RUNNER = ('f=$(mktemp) && cat >"$f" && chmod +x "$f" && '
               'timeout "$2" qemu-riscv64 -cpu "$1" "$f"; rc=$?; rm -f "$f"; exit $rc')


def retarget_mir(mir: str) -> str:
    """Normalize per-function features, which override llc's -mattr, to our target."""
    return re.sub(r'"target-features"="[^"]*"', f'"target-features"="{FEATURES}"', mir)
