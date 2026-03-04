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
  Adds the sign-extended 12-bit immediate to register rs1. Arithmetic overflow is ignored and the
  result is simply the low 64 bits of the result. ADDI rd, rs1, 0 is used to implement the MV
  rd, rs1 assembler pseudo-instruction.
-/
def addi (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
  BitVec.add rs1_val immext

/--
  Place the value 1 in register rd if register rs1 is less than the signextended immediate when
  both are treated as signed numbers, else 0 is written to rd.
-/
def slti (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  let b := BitVec.slt rs1_val immext
  BitVec.zeroExtend 64 (BitVec.ofBool b)

/--
  Place the value 1 in register rd if register rs1 is less than the immediate when both are
  treated as unsigned numbers, else 0 is written to rd.
-/
def sltiu (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  let b := BitVec.ult rs1_val immext
  BitVec.setWidth 64 (BitVec.ofBool b)

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

/--
  Adds the sign-extended 12-bit immediate to register rs1 and produces the proper sign-extension
  of a 32-bit result in rd. Overflows are ignored and the result is the low 32 bits of the result
  sign-extended to 64 bits. Note, ADDIW rd, rs1, 0 writes the sign-extension of the lower 32 bits
  of register rs1 into register rd (assembler pseudoinstruction SEXT.W).
-/
def addiw (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.setWidth 32 ((BitVec.signExtend 64 imm) + rs1_val))

/--
  Performs logical left shift on the value in register rs1 by the shift amount held in the lower 6
  bits of the immediate in RV64.
-/
def slli (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 := rs1_val <<< shamt

/--
  Performs logical right shift on the value in register rs1 by the shift amount held in the lower 6
  bits of the immediate in RV64.
-/
def srli (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 := rs1_val >>> shamt

/--
  Performs arithmetic right shift on the value in register rs1 by the shift amount held in the
  lower 6 bits of the immediate in RV64.
-/
def srai (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.sshiftRight' rs1_val shamt)
