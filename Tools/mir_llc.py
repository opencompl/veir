"""llc invocations that turn VeIR's pre-RA RISC-V MIR (from veir2mir) into assembly.

Shared by vcc and vsmith.
"""

from __future__ import annotations

import functools
import re
import subprocess

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

# LLVM 24 renamed several legacy machine passes to match their new-PM names;
# -run-pass/-start-after on LLVM <= 23 only accept the old ones.
LLVM23_PASS_NAMES = {
    "two-address-instruction": "twoaddressinstruction",
    "virt-reg-rewriter": "virtregrewriter",
    "post-ra-pseudos": "postrapseudos",
    "riscv-expand-pseudo-pre-emit": "riscv-expand-pseudo",
}


@functools.lru_cache(maxsize=None)
def llc_major_version(llc: str) -> int:
    out = subprocess.run([llc, "--version"], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, check=True).stdout
    m = re.search(r"LLVM version (\d+)", out)
    if m is None:
        raise RuntimeError(f"cannot determine LLVM version of {llc}:\n{out}")
    return int(m.group(1))


def pass_name(llc: str, name: str) -> str:
    """`name` (LLVM 24 spelling) as accepted by this llc."""
    if llc_major_version(llc) <= 23:
        return LLVM23_PASS_NAMES.get(name, name)
    return name


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
