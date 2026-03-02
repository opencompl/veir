module

namespace Veir.Data.RISCV

public section

/--
The `reg` type is a wrapper around a `reg` representing the content of a register.

-/
abbrev Reg := BitVec 64

/-!
  The semantics are proven equivalent to the authoritative Sail model,
  and are taken from https://github.com/opencompl/riscv-lean.
  We should always remain consistent with those semantics.
-/

/-! # RV64I Base Integer Instruction Set -/

/--
  Load a 64-wide immediate into the destination register rd
-/
def li (imm : BitVec 64) : Reg :=
  imm

/--
  Build 32-bit constants and uses the U-type format. LUI places the U-immediate value in the top 20
  bits of the destination register rd, filling in the lowest 12 bits with zeros.
-/
def lui (imm : BitVec 20) : Reg :=
  (imm ++ (0x0 : BitVec 12)).signExtend 64

/--
  Build pc-relative addresses and uses the U-type format. AUIPC forms a 32-bit offset from the
  20-bit U-immediate, filling in the lowest 12 bits with zeros, adds this offset to the pc,
  then places the result in register rd.
-/
def auipc (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x0 : BitVec 12))) pc

/--
  Performs bitwise AND on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd.
-/
def andi (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  BitVec.and rs1_val immext

/--
  Performs bitwise OR on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd.
-/
def ori (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  BitVec.or rs1_val immext

/--
  Performs bitwise XOR on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd Note, "XORI rd, rs1, -1" performs a bitwise logical inversion of register rs1
  (assembler pseudo-instruction NOT rd, rs)
-/
def xori (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  BitVec.xor rs1_val immext
