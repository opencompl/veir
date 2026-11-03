"""llc invocations that turn VeIR's pre-RA RISC-V MIR (from veir2mir) into assembly.

Shared by vcc and vsmith.
"""

from __future__ import annotations

import functools
import subprocess

# Register-allocation stage: MIR -> fully-lowered MIR. Rather than a canned
# -O0/-O2 pipeline we drive an explicit minimal machine pipeline via -run-pass
# so VeIR's instruction selection passes through unmodified while we still get
# the greedy allocator: PHI elimination, two-address lowering, register
# coalescing (deletes isel-generated copies), greedy allocation +
# virtual-register rewriting, prologue/epilogue insertion, and post-RA / RISCV
# pseudo expansion. riscv-expand-pseudo-post-ra is needed for large frames:
# frame-index elimination emits PseudoAddUpperImm, which the asm printer can't
# print. -run-pass emits MIR, so the asm printer runs in a second
# stage.
REGALLOC_PASSES = (
    "phi-node-elimination,two-address-instruction,register-coalescer,greedy,"
    "virt-reg-rewriter,prolog-epilog,post-ra-pseudos,riscv-expand-pseudo-post-ra,"
    "riscv-expand-pseudo-pre-emit"
)

# LLVM 24 renamed several legacy machine passes to match their new-PM names;
# -run-pass/-start-after on LLVM <= 23 only accept the old ones. The renames
# landed in separate commits, so a 24.0.0git llc may accept any mix of the
# two spellings; pass_name probes each one rather than trusting the version.
LLVM23_PASS_NAMES = {
    "two-address-instruction": "twoaddressinstruction",
    "virt-reg-rewriter": "virtregrewriter",
    "post-ra-pseudos": "postrapseudos",
    "riscv-expand-pseudo-post-ra": "riscv-post-ra-expand-pseudo",
    "riscv-expand-pseudo-pre-emit": "riscv-expand-pseudo",
}


@functools.lru_cache(maxsize=None)
def pass_registered(llc: str, name: str) -> bool:
    """Whether this llc accepts `name` as a -run-pass argument."""
    result = subprocess.run(
        [llc, "-mtriple=riscv64", "-x", "mir", f"-run-pass={name}",
         "-o", "/dev/null", "/dev/null"],
        stdin=subprocess.DEVNULL, capture_output=True, text=True)
    return "is not registered" not in result.stderr


def pass_name(llc: str, name: str) -> str:
    """`name` (LLVM 24 spelling) as accepted by this llc."""
    old = LLVM23_PASS_NAMES.get(name)
    if old is None or pass_registered(llc, name):
        return name
    return old


def regalloc_cmd(llc: str, mir: str, lowered: str) -> list[str]:
    passes = ",".join(pass_name(llc, p) for p in REGALLOC_PASSES.split(","))
    return [llc, mir, "-mtriple=riscv64", "-x", "mir", f"-run-pass={passes}",
            "-o", lowered]


def emit_asm_cmd(llc: str, lowered: str, asm: str) -> list[str]:
    """Emission stage: fully-lowered MIR -> RISC-V assembly. Starting after the
    last regalloc-stage pass skips straight to the asm printer (the few
    remaining passes are no-ops here) without re-running regalloc or prologue
    insertion, which would corrupt the already-lowered MIR. Direct object
    emission isn't possible: pseudos like PseudoLLA are only expanded by the
    assembler."""
    return [llc, lowered, "-mtriple=riscv64", "-x", "mir",
            f"-start-after={pass_name(llc, 'riscv-expand-pseudo-pre-emit')}",
            "-o", asm]
