"""llc invocations that turn VeIR's pre-RA RISC-V MIR (from veir2mir) into assembly.

Shared by vcc and vsmith.
"""

from __future__ import annotations

# Register-allocation stage: MIR -> fully-lowered MIR. Rather than a canned
# -O0/-O2 pipeline we drive an explicit minimal machine pipeline via -run-pass
# so VeIR's instruction selection passes through unmodified while we still get
# the greedy allocator: PHI elimination, two-address lowering, register
# coalescing (deletes isel-generated copies), greedy allocation +
# virtual-register rewriting, prologue/epilogue insertion, and post-RA / RISCV
# pseudo expansion. -run-pass emits MIR, so the asm printer runs in a second
# stage.
REGALLOC_PASSES = (
    "phi-node-elimination,two-address-instruction,register-coalescer,greedy,"
    "virt-reg-rewriter,prolog-epilog,post-ra-pseudos,riscv-expand-pseudo-pre-emit"
)


def regalloc_cmd(llc: str, mir: str, lowered: str) -> list[str]:
    return [llc, mir, "-mtriple=riscv64", "-x", "mir", f"-run-pass={REGALLOC_PASSES}",
            "-o", lowered]


def emit_asm_cmd(llc: str, lowered: str, asm: str) -> list[str]:
    """Emission stage: fully-lowered MIR -> RISC-V assembly. Starting after the
    last regalloc-stage pass skips straight to the asm printer (the few
    remaining passes are no-ops here) without re-running regalloc or prologue
    insertion, which would corrupt the already-lowered MIR. Direct object
    emission isn't possible: pseudos like PseudoLLA are only expanded by the
    assembler."""
    return [llc, lowered, "-mtriple=riscv64", "-x", "mir",
            "-start-after=riscv-expand-pseudo-pre-emit", "-o", asm]
