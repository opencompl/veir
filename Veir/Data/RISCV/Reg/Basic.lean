module

namespace Veir.Data.RISCV

public section

/--
The `Reg` type is a `BitVec 64` representing the content of a register.
-/
structure Reg where
  val : BitVec 64

instance : ToString Reg where
  toString r := toString r.val

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
  ⟨imm⟩

/--
  Build 32-bit constants and uses the U-type format. LUI places the U-immediate value in the top 20
  bits of the destination register rd, filling in the lowest 12 bits with zeros.
-/
def lui (imm : BitVec 20) : Reg :=
  ⟨(imm ++ (0x0 : BitVec 12)).signExtend 64⟩

/--
  Build pc-relative addresses and uses the U-type format. AUIPC forms a 32-bit offset from the
  20-bit U-immediate, filling in the lowest 12 bits with zeros, adds this offset to the pc,
  then places the result in register rd.
-/
def auipc (imm : BitVec 20) (pc : Reg) : Reg :=
  ⟨BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x0 : BitVec 12))) pc.val⟩

/--
  Adds the sign-extended 12-bit immediate to register rs1. Arithmetic overflow is ignored and the
  result is simply the low 64 bits of the result. ADDI rd, rs1, 0 is used to implement the MV
  rd, rs1 assembler pseudo-instruction.
-/
def addi (imm : BitVec 12) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  ⟨BitVec.add rs1.val immext⟩

/--
  Place the value 1 in register rd if register rs1 is less than the signextended immediate when
  both are treated as signed numbers, else 0 is written to rd.
-/
def slti (imm : BitVec 12) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  let b := BitVec.slt rs1.val immext
  ⟨BitVec.zeroExtend 64 (BitVec.ofBool b)⟩

/--
  Place the value 1 in register rd if register rs1 is less than the immediate when both are
  treated as unsigned numbers, else 0 is written to rd.
-/
def sltiu (imm : BitVec 12) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  let b := BitVec.ult rs1.val immext
  ⟨BitVec.setWidth 64 (BitVec.ofBool b)⟩

/--
  Performs bitwise AND on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd.
-/
def andi (imm : BitVec 12) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  ⟨BitVec.and rs1.val immext⟩

/--
  Performs bitwise OR on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd.
-/
def ori (imm : BitVec 12) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  ⟨BitVec.or rs1.val immext⟩

/--
  Performs bitwise XOR on register rs1 and the sign-extended 12-bit immediate and place the result
  in rd Note, "XORI rd, rs1, -1" performs a bitwise logical inversion of register rs1
  (assembler pseudo-instruction NOT rd, rs)
-/
def xori (imm : (BitVec 12)) (rs1 : Reg) : Reg :=
  let immext : BitVec 64 := (BitVec.signExtend 64 imm)
  ⟨BitVec.xor rs1.val immext⟩

/--
  Adds the sign-extended 12-bit immediate to register rs1 and produces the proper sign-extension
  of a 32-bit result in rd. Overflows are ignored and the result is the low 32 bits of the result
  sign-extended to 64 bits. Note, ADDIW rd, rs1, 0 writes the sign-extension of the lower 32 bits
  of register rs1 into register rd (assembler pseudoinstruction SEXT.W).
-/
def addiw (imm : BitVec 12) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 (BitVec.setWidth 32 ((BitVec.signExtend 64 imm) + rs1.val))⟩

/--
  Performs logical left shift on the value in register rs1 by the shift amount held in the lower 6
  bits of the immediate in RV64.
-/
def slli (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨rs1.val <<< shamt⟩

/--
  Performs logical right shift on the value in register rs1 by the shift amount held in the lower 6
  bits of the immediate in RV64.
-/
def srli (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨rs1.val >>> shamt⟩

/--
  Performs arithmetic right shift on the value in register rs1 by the shift amount held in the
  lower 6 bits of the immediate in RV64.
-/
def srai (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 (BitVec.sshiftRight' rs1.val shamt)⟩

/--
  Adds the registers rs1 and rs2 and stores the result in rd. Arithmetic overflow is ignored and
  the result is simply the low 64 bits of the result.
-/
def add (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val + rs2.val⟩

/--
  Subtracts the register rs2 from rs1 and stores the result in rd. Arithmetic overflow is ignored and
  the result is simply the low 64 bits of the result.
-/
def sub (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val - rs2.val⟩

/--
  Performs logical left shift on the value in register rs1 by the shift amount held in the lower 5
  bits of register rs2.
-/
def sll (rs2 : Reg) (rs1 : Reg) : Reg :=

  let shamt := (BitVec.extractLsb 5 0 rs2.val);
  ⟨rs1.val <<< shamt⟩

/--
  Place the value 1 in register rd if register rs1 is less than register rs2 when both are treated
  as signed numbers, else 0 is written to rd.
-/
def slt (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.setWidth 64 (BitVec.ofBool (BitVec.slt rs1.val rs2.val))⟩

/--
  Place the value 1 in register rd if register rs1 is less than register rs2 when both are treated
  as unsigned numbers, else 0 is written to rd.
-/
def sltu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.setWidth 64 (BitVec.ofBool (BitVec.ult rs1.val rs2.val))⟩

/--
  Performs bitwise XOR on registers rs1 and rs2 and place the result in rd.
-/
def xor (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val ^^^ rs2.val⟩

/--
  Logical right shift on the value in register rs1 by the shift amount held in the lower 5 bits of
  register rs2.
-/
def srl (rs2 : Reg) (rs1 : Reg) : Reg :=

  let shamt := (BitVec.extractLsb 5 0 rs2.val)
  ⟨rs1.val >>> shamt⟩

/--
  Performs arithmetic right shift on the value in register rs1 by the shift amount held in the
  lower 5 bits of register rs2.
-/
def sra (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.sshiftRight' rs1.val (BitVec.extractLsb 5 0 rs2.val)⟩

/--
  Performs bitwise OR on registers rs1 and rs2 and place the result in rd.
-/
def or (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val ||| rs2.val⟩

/--
  Performs bitwise AND on registers rs1 and rs2 and place the result in rd.
-/
def and (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val &&& rs2.val⟩

/--
  Performs logical left shift on the lowest 32 bits of the value in rs1 by the shift amount held in
  the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def slliw (shamt : BitVec 5) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 ((BitVec.extractLsb' 0 32 rs1.val) <<< shamt)⟩

/--
  Performs logical right shift on the lowest 32 bits of the value in rs1 by the shift amount held in
  the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def srliw (shamt : BitVec 5) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 ((BitVec.extractLsb' 0 32 rs1.val) >>> shamt)⟩

/--
  Performs arithmetic right shift on the lowest 32 bits of rs1 by the shift amount held
  in the lower 5 bits of the immediate. Encodings with $imm[5] neq 0$ are reserved.
-/
def sraiw (shamt : BitVec 5) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 (BitVec.sshiftRight' (BitVec.extractLsb 31 0 rs1.val) shamt)⟩

/--
  Adds the lowest 32 bits of rs1 and the lowest 32 bits of rs2, and stores the result in rd.
  Arithmetic overflow is ignored and the lowest 32-bits of the result are sign-extended to 64 bits and
  written to the destination register.
-/
def addw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb' 0 32 rs1.val
  let rs2w := BitVec.extractLsb' 0 32 rs2.val
  ⟨BitVec.signExtend 64 (BitVec.add rs1w rs2w)⟩

/--
  Subtract the lowest 32 bits of rs1 and the lowest 32 bits of rs2, and stores the result in rd.
  Arithmetic overflow is ignored and the lowest 32 bits of the result are sign-extended to 64 bits and
  written to the destination register.
-/
def subw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb' 0 32 rs1.val
  let rs2w := BitVec.extractLsb' 0 32 rs2.val
  ⟨BitVec.signExtend 64 (BitVec.sub rs1w rs2w)⟩

/--
  Performs logical left shift on the lowest 32 bits of rs1 by the shift amount held in
  the lower 5 bits of rs2, and produce a 32-bit result that is sign-extended to 64 bits and
  written to the destination register rd.
-/
def sllw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb' 0 32 rs1.val;
  let rs2w := BitVec.extractLsb' 0 32 rs2.val;
  let shamt := BitVec.extractLsb' 0 5 rs2w;
  ⟨BitVec.signExtend 64 (rs1w <<< shamt)⟩

/--
  Performs logical right shift on the lowest 32 bits of rs1 by the shift amount held in
  the lowest 5 bits of rs2, and produce a 32-bit result that is sign-extended to 64 bits and
  written to the destination register rd.
-/
def srlw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb' 0 32 rs1.val;
  let rs2w := BitVec.extractLsb' 0 32 rs2.val;
  let shamt := BitVec.extractLsb' 0 5 rs2w;
  ⟨BitVec.signExtend 64 (rs1w >>> shamt)⟩

/--
  Performs arithmetic right shift on the lowest 32 bits of rs1 by the shift amount held
  in the lowest 5 bits of rs2, and produce a 32-bit result that is sign-extended to 64 bits and
  written to the destination register rd.
-/
def sraw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 4 0 rs2.val
  ⟨BitVec.signExtend 64 (BitVec.sshiftRight' rs1w rs2w)⟩

/-! # M Extension for Integer Multiplication and Division -/

/--
  Perform a 64-bits by 64-bits signed integer reminder of rs1 by rs2.
-/
def rem (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val.srem rs2.val⟩

/--
  Perform a 64-bits by 64-bits unsigned integer reminder of rs1 by rs2.
-/
def remu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val.umod rs2.val⟩

/--
  Perform a 32-bits by 32-bits signed integer reminder of rs1 by rs2.
-/
def remw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 31 0 rs2.val
  ⟨BitVec.signExtend 64 (rs1w.srem rs2w)⟩

/--
  Perform a 32-bits by 32-bits unsigned integer reminder of rs1 by rs2.
-/
def remuw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 31 0 rs2.val
  ⟨BitVec.signExtend 64 (rs1w.umod rs2w)⟩

/--
  Performs a 64-bits times 64-bits multiplication of signed rs1 by signed rs2.
-/
def mul (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs2.val * rs1.val⟩

/--
  Performs a 64-bits times 64-bits multiplication of signed rs1 by signed rs2 and places the highest 64 bits in the destination register.
-/
def mulh (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb 127 64 ((BitVec.signExtend 129 rs1.val) * (BitVec.signExtend 129 rs2.val))⟩

/--
  Performs a 64-bits times 64-bits multiplication of unsigned rs1 by unsigned rs2 and places the highest 64 bits in the destination register.
-/
def mulhu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb 127 64
  (BitVec.extractLsb' 0 128 ((BitVec.zeroExtend 128 rs1.val) * (BitVec.zeroExtend 128 rs2.val)))⟩

/--
  Performs a 64-bits times 64-bits multiplication of signed rs1 by unsigned rs2 and places the highest 64 bits in the destination register.
-/
def mulhsu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb 127 64 (((BitVec.signExtend 129 rs1.val) * (BitVec.zeroExtend 129 rs2.val)))⟩

/--
  Multiplies the lowest 32 bits of rs1 by the lowest 32 bits of rs2,
  placing the sign extension of the lowest 32 bits of the result into the destination register.
-/
def mulw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 31 0 rs2.val
  ⟨BitVec.signExtend 64
    (((BitVec.extractLsb 31 0 rs1w) * (BitVec.extractLsb 31 0 rs2w)))⟩

/--
  Perform a 64-bits by 64-bits signed integer division of rs1 by rs2, rounding towards zero.
-/
def div (rs2 : Reg) (rs1 : Reg) : Reg :=
  if rs2.val = 0#64 then
    ⟨-1#64⟩
  else
    ⟨rs1.val.sdiv rs2.val⟩

/--
  Performs signed division of the lowest 32 bits of rs1 by the lowest 32 bits of rs2
  placing the sign extension of the lowest 32 bits of the result into the destination register.
-/
def divw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 31 0 rs2.val
  ⟨BitVec.signExtend 64 (if rs2w = 0#32 then  -1#32 else rs1w.sdiv rs2w)⟩

/--
  Perform a 64-bits by 64-bits unsigned integer division of rs1 by rs2.
-/
def divu (rs2 : Reg) (rs1 : Reg) : Reg :=
  if rs2.val = 0#64 then ⟨(-1)⟩ else ⟨rs1.val.udiv rs2.val⟩

/--
  Performs unsigned division of the lowest 32 bits of rs1 by the lowest 32 bits of rs2,
  placing the sign extension of the lowest 32 bits of the result into the destination register.
-/
def divuw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let rs2w := BitVec.extractLsb 31 0 rs2.val
  ⟨BitVec.signExtend 64 (if rs2w = 0#32 then -1#32 else rs1w.udiv rs2w)⟩

/-! # "B" Extension for Bit Manipulation -/

/-! ## Zba: Address generation -/

/--
  This instruction performs an 64-wide addition between rs2 and the zero-extended
  least-significant word of rs1.
-/
def adduw (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1.val) <<< 0#2 + rs2.val⟩

/--
 This instruction performs an 64-bits addition of two addends.
 The first addend is rs2. The second addend is the unsigned value formed by extracting the
 least-significant word of rs1 and shifting it left by 1 place.
-/
def sh1adduw (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1.val) <<< 1#2 + rs2.val⟩

/--
  This instruction performs an 64-bits addition of two addends.
  The first addend is rs2. The second addend is the unsigned value formed by extracting the
  least-significant word of rs1 and shifting it left by 2 places.
-/
def sh2adduw (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1.val) <<< 2#2 + rs2.val⟩

/--
    This instruction performs an 64-bits addition of two addends.
    The first addend is rs2. The second addend is the unsigned value formed by extracting the
    least-significant word of rs1 and shifting it left by 3 places.
-/
def sh3adduw (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1.val) <<< 3#2 + rs2.val⟩

/--
  This instruction shifts rs1 to the left by 1 bit and adds it to rs2.
-/
def sh1add (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val <<< 1#2 + rs2.val⟩

/--
  This instruction shifts rs1 to the left by 2 places and adds it to rs2.
-/
def sh2add (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val <<< 2#2 + rs2.val⟩

/--
  This instruction shifts rs1 to the left by 3 places and adds it to rs2.
-/
def sh3add (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val <<< 3#2 + rs2.val⟩

/--
  This instruction takes the least-significant word of rs1, zero-extends it,
  and shifts it left by the immediate.
-/
def slliuw (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨(BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1.val)) <<< shamt⟩

/-! ## Zbb: Basic bit-manipulation -/

/--
  This instruction performs the bitwise logical AND operation between rs1 and the bitwise inversion of rs2.
-/
def andn (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val &&& ~~~rs2.val⟩

/--
  This instruction performs the bitwise logical OR operation between rs1 and the bitwise inversion of rs2.
-/
def orn (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val ||| ~~~rs2.val⟩

/--
  This instruction performs the bit-wise exclusive-NOR operation on rs1 and rs2.
-/
def xnor (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨~~~ (rs1.val ^^^ rs2.val)⟩

/--
  This instruction returns the larger of two signed integers.
-/
def max (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb' 0 64 (if BitVec.slt rs2.val rs1.val then rs1.val else rs2.val)⟩

/--
  This instruction returns the larger of two unsigned integers.
-/
def maxu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb' 0 64 (if BitVec.ult rs2.val rs1.val then rs1.val else rs2.val)⟩

/--
  This instruction returns the smaller of two signed integers.
-/
def min (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb' 0 64 (if BitVec.slt rs1.val rs2.val then rs1.val else rs2.val)⟩

/--
  This instruction returns the smaller of two unsigned integers.
-/
def minu (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb' 0 64 (if BitVec.ult rs1.val rs2.val then rs1.val else rs2.val)⟩

/--
  This instruction performs a rotate left of rs1 by the amount in least-significant log2(64) bits of rs2.
-/
def rol (rs2 : Reg) (rs1 : Reg) : Reg :=
  let shamt := BitVec.extractLsb 5 0 rs2.val
  ⟨(rs1.val <<< shamt) ||| (rs1.val >>> (64#6 - shamt))⟩

/--
  This instruction performs a rotate right of rs1 by the amount in least-significant log2(64) bits of rs2.
-/
def ror (rs2 : Reg) (rs1 : Reg) : Reg :=
  let shamt := BitVec.extractLsb 5 0 rs2.val
  ⟨(rs1.val >>> shamt) ||| (rs1.val <<< (64#6 - shamt))⟩

/--
  This instruction performs a rotate left on the least-significant word of rs1 by the amount in
  least-significant 5 bits of rs2.
  The resulting word value is sign-extended by copying bit 31 to all of the more-significant bits.
-/
def rolw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let shamt := BitVec.extractLsb 4 0 rs2.val
  ⟨BitVec.signExtend 64 ((rs1w <<< shamt) ||| (rs1w >>> (32#5 - shamt)))⟩

/--
  This instruction performs a rotate right on the least-significant word of rs1 by the amount in
  least-significant 5 bits of rs2.
  The resultant word is sign-extended by copying bit 31 to all of the more-significant bits.
-/
def rorw (rs2 : Reg) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  let shamt := BitVec.extractLsb 4 0 rs2.val
  ⟨BitVec.signExtend 64 ((rs1w >>> shamt) ||| (rs1w <<< (32#5 - shamt)))⟩

/--
  This instruction sign-extends the least-significant byte in the source to 64 by copying the
  most-significant bit in the byte (i.e., bit 7) to all of the more-significant bits.
-/
def sextb (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 (BitVec.extractLsb 7 0 rs1.val)⟩

/--
  This instruction sign-extends the least-significant halfword in rs to 64 by copying the
  most-significant bit in the halfword (i.e., bit 15) to all of the more-significant bits.
-/
def sexth (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64 (BitVec.extractLsb 15 0 rs1.val)⟩

/--
  Zero-extend halfword.
-/
def zexth (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.extractLsb 15 0 rs1.val)⟩

/--
  This instruction counts the number of 0’s before the first 1, starting at the most-significant bit
  (i.e., 64-1) and progressing to bit 0. Accordingly, if the input is 0, the output is 64, and
  if the most-significant bit of the input is a 1, the output is 0.
-/
def clz (rs1 : Reg) : Reg :=
  ⟨BitVec.clz rs1.val⟩

/--
  This instruction counts the number of 0’s before the first 1 starting at bit 31 and progressing
  to bit 0. Accordingly, if the least-significant word is 0, the output is 32, and if the
  most-significant bit of the word (i.e., bit 31) is a 1, the output is 0.
-/
def clzw (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.clz (BitVec.extractLsb 31 0 rs1.val))⟩

/--
  This instruction counts the number of 0’s before the first 1, starting at the least-significant
  bit (i.e., 0) and progressing to the most-significant bit (i.e., 64-1). Accordingly, if the
  input is 0, the output is 64, and if the least-significant bit of the input is a 1, the output is 0.
-/
def ctz (rs1 : Reg) : Reg :=
  ⟨BitVec.ctz rs1.val⟩

/--
  This instruction counts the number of 0’s before the first 1, starting at the least-significant
  bit (i.e., 0) and progressing to the most-significant bit of the least-significant word (i.e., 31).
  Accordingly, if the least-significant word is 0, the output is 32, and if the least-significant
  bit of the input is a 1, the output is 0.
-/
def ctzw (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64 (BitVec.ctz (BitVec.extractLsb 31 0 rs1.val))⟩

/--
  This instructions counts the number of 1’s (i.e., set bits) in the source register.
-/
def cpop (rs1 : Reg) : Reg :=
  ⟨BitVec.cpop rs1.val⟩

/--
  This instructions counts the number of 1’s (i.e., set bits) in the least-significant word of the
  source register.
-/
def cpopw (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  ⟨BitVec.zeroExtend 64 (BitVec.cpop rs1w)⟩
/--
  This instruction performs a rotate right on the least-significant word of rs1 by the amount in the
  least-significant log2(64) bits of shamt. The resulting word value is sign-extended by
  copying bit 31 to all of the more-significant bits.
-/
def roriw (shamt : BitVec 5) (rs1 : Reg) : Reg :=
  let rs1w := BitVec.extractLsb 31 0 rs1.val
  ⟨BitVec.signExtend 64 ((rs1w >>> shamt) ||| (rs1w <<< (32 - shamt)))⟩

/--
  This instruction performs a rotate right of rs1 by the amount in the least-significant log2(64)
  bits of shamt. For RV32, the encodings corresponding to shamt[5]=1 are reserved.
-/
def rori (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨(rs1.val >>> shamt) ||| (rs1.val <<< (64 - shamt))⟩

/-! ## Zbc: Carry-less multiplication -/

/-! ## Zbs: Single-bit instructions -/

/--
  This instruction returns rs1 with a single bit cleared at the index specified
  in rs2. The index is read from the lower log2(64) bits of rs2.
-/
def bclr (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val &&& (~~~((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb 5 0 rs2.val)))⟩

/--
  This instruction returns a single bit extracted from rs1 at the index specified in rs2.
  The index is read from the lower log2(64) bits of rs2.
-/
def bext (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.setWidth 64
    (if (rs1.val &&&
      ((BitVec.setWidth 64 1#1) <<< (BitVec.extractLsb 5 0 rs2.val)) != 0#64) then 1#1 else 0#1)⟩

/--
  This instruction returns rs1 with a single bit inverted at the index specified in rs2.
  The index is read from the lower log2(64) bits of rs2.
-/
def binv (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val ^^^ ((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb 5 0 rs2.val))⟩

/--
  This instruction returns rs1 with a single bit set at the index specified in rs2.
  The index is read from the lower log2(64) bits of rs2.
-/
def bset (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨rs1.val ||| ((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb 5 0 rs2.val))⟩

/--
  This instruction returns rs1 with a single bit cleared at the index specified in shamt.
  The index is read from the lower log2(64) bits of shamt.
  For RV32, the encodings corresponding to shamt[5]=1 are reserved.
-/
def bclri (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨rs1.val &&& (~~~((BitVec.setWidth 64 1#1) <<< shamt))⟩

/--
  This instruction returns a single bit extracted from rs1 at the index specified in shamt.
  The index is read from the lower log2(64) bits of shamt.
  For RV32, the encodings corresponding to shamt[5]=1 are reserved.
-/
def bexti (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨BitVec.setWidth 64 (if (rs1.val &&& ((BitVec.setWidth 64 1#1) <<< shamt)) != 0#64 then 1#1 else 0#1)⟩

/--
  This instruction returns rs1 with a single bit inverted at the index specified in shamt.
  The index is read from the lower log2(64) bits of shamt.
  For RV32, the encodings corresponding to shamt[5]=1 are reserved.
-/
def binvi (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨rs1.val ^^^ ((BitVec.zeroExtend 64 1#1) <<< shamt)⟩

/--
  This instruction returns rs1 with a single bit set at the index specified in shamt.
  The index is read from the lower log2(64) bits of shamt.
  For RV32, the encodings corresponding to shamt[5]=1 are reserved.
-/
def bseti (shamt : BitVec 6) (rs1 : Reg) : Reg :=
  ⟨rs1.val ||| ((BitVec.zeroExtend 64 1#1) <<< shamt)⟩

/-! ## Zbkb: Bit-manipulation for Cryptography-/

/--
  Pack the low halves of rs1 and rs2 into rd.
-/
def pack (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.extractLsb 31 0 rs2.val ++ BitVec.extractLsb 31 0 rs1.val⟩

/--
  Pack the low bytes of rs1 and rs2 into rd.
-/
def packh (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.zeroExtend 64
    ((BitVec.extractLsb 7 0 rs2.val) ++ (BitVec.extractLsb 7 0 rs1.val))⟩

/--
  Pack the low 16-bits of rs1 and rs2 into rd on RV64.
-/
def packw (rs2 : Reg) (rs1 : Reg) : Reg :=
  ⟨BitVec.signExtend 64
    ((BitVec.extractLsb 15 0 rs2.val) ++ (BitVec.extractLsb 15 0 rs1.val))⟩

/-! ## Zbkc: Carry-less multiplication for Cryptography -/

/-! ## Zbkx: Carry-less multiplication for Cryptography -/
