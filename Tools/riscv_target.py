"""RISC-V Linux target shared by the compiler drivers and QEMU.

Keep the triple, ABI and features in sync with Veir/MIRPrinter.lean, which
emits them directly into standalone MIR along with the lp64d call masks.
"""

TRIPLE = "riscv64-unknown-linux-gnu"
ABI = "lp64d"
VEIR_EXTENSIONS = ("zba", "zbb", "zbs", "zbc", "zbkb", "zicond")
MARCH = "rv64gc_" + "_".join(VEIR_EXTENSIONS)
# Expand G for llc, which accepts individual features rather than -march.
FEATURES = ",".join(f"+{ext}" for ext in
                    ("m", "a", "f", "d", "c", "zicsr", "zifencei", *VEIR_EXTENSIONS))
CLANG_TARGET_FLAGS = (f"--target={TRIPLE}", f"-march={MARCH}", f"-mabi={ABI}")
LLC_TARGET_FLAGS = (f"-mtriple={TRIPLE}", f"-mattr={FEATURES}", f"-target-abi={ABI}")
# QEMU's rv64 CPU already enables rv64gc.
QEMU_CPU = "rv64," + ",".join(f"{ext}=true" for ext in VEIR_EXTENSIONS)
