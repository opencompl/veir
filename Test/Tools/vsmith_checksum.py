"""Check that changing any accessed byte changes the generated checksum."""

from __future__ import annotations

import random
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "Tools"))
from vsmith_generate import Generator, MEM_ALIGN_PROPS


def program(changed_byte: int | None) -> str:
    gen = Generator(random.Random(0), riscv=True)
    count = gen.add_const("i64", 32)
    gen.lines.append(f'  %mem = "llvm.alloca"({count}) <{{elem_type = i8}}> : (i64) -> !llvm.ptr')
    # Two overlapping windows, a disjoint window, and a repeated pointer.
    # Repeating a value would cancel in a checksum consisting of plain XORs.
    offsets = (0, 7, 24, 0)
    gen.ptrs = [(gen.byte_gep("%mem", offset), offset) for offset in offsets]
    gen.init_region("%mem")
    if changed_byte is not None:
        ptr = gen.byte_gep("%mem", changed_byte)
        old = gen.add_operation("llvm.load", [ptr], ["!llvm.ptr"], "i8", MEM_ALIGN_PROPS)
        one = gen.add_const("i8", 1)
        new = gen.add_operation("llvm.xor", [old, one], ["i8", "i8"], "i8")
        gen.lines.append(f'  "llvm.store"({new}, {ptr}){MEM_ALIGN_PROPS} : (i8, !llvm.ptr) -> ()')
    result = gen.memory_checksum()
    gen.lines.append(f'  "llvm.return"({result}) : (i64) -> ()')
    return '\n'.join([
        '"builtin.module"() ({',
        '  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({',
        *gen.lines,
        '  }) : () -> ()',
        '}) : () -> ()',
    ])


with tempfile.TemporaryDirectory(prefix="vsmith-checksum-") as tmp:
    path = Path(tmp) / "checksum.mlir"

    def run(changed_byte: int | None) -> str:
        path.write_text(program(changed_byte))
        result = subprocess.run([str(REPO / ".lake/build/bin/veir-interpret"), str(path)],
                                capture_output=True, text=True, check=True)
        assert result.stdout.startswith("Program output: #[0x"), result.stdout
        return result.stdout

    baseline = run(None)
    # Includes the tail of the first merged window and both allocation edges.
    for offset in [*range(15), *range(24, 32)]:
        assert run(offset) != baseline, f"checksum ignored byte {offset}"
