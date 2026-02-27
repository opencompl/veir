module

namespace Veir.Data.RISCV

public section

/--
The `reg` type is a wrapper around a `reg` representing the content of a register.

-/
abbrev reg := BitVec 64

/-!
  The semantics are proven equivalent to the authoritative Sail model,
  and are taken from https://github.com/opencompl/riscv-lean.
  We should always remain consistent with those semantics.
-/

/-! # RV64I Base Integer Instruction Set -/

/--
  Load a 64-wide immediate into the destination register rd
-/
def li (imm : BitVec 64) : reg :=
  imm

/--
  Build 32-bit constants and uses the U-type format. LUI places the U-immediate value in the top 20
  bits of the destination register rd, filling in the lowest 12 bits with zeros.
-/
def lui (imm : BitVec 20) : reg :=
  BitVec.signExtend 64 (imm ++ (0x0 : BitVec 12))
