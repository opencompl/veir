"""RISC-V Linux target shared by the compiler drivers and QEMU.

Keep the triple, ABI and features in sync with Veir/MIRPrinter.lean, which
emits them directly into standalone MIR along with the lp64d call masks.
"""

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
