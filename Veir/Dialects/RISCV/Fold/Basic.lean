module

public import Veir.Dialects.RISCV.OpInfo.Basic

public section

namespace Veir

/--
  Fold table for `riscv` operations with partially-constant operands.

  Register-register operations are interpreted as `RISCV.f rs2 rs1` with
  `rs1 = operands[0]` and `rs2 = operands[1]`, so the identities below key off
  a constant `operands[1]`. RISC-V registers have no poison, and division by
  zero is defined (it is handled by generic all-constant evaluation), so no
  entry here produces poison. Immediate-carrying operations (`addi`, `slli`,
  ...) fold on their properties instead of an operand.
-/
def Riscv.foldsTo (op : Riscv) (properties : Riscv.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .add => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sub => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .xor => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .or => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useOperand 0
      else if c.val = BitVec.allOnes 64 then
        .useConstant (.reg (Data.RISCV.li (BitVec.allOnes 64)))
      else .noFold
    | _ => .noFold
  | .and => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else if c.val = BitVec.allOnes 64 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .mul => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else if c.val = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .sll => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srl => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sra => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .czeroeqz => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else .useOperand 0
    | _ => .noFold
  | .czeronez => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useOperand 0
      else .useConstant (.reg (Data.RISCV.li 0))
    | _ => .noFold
  | .addi => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .ori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .xori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .andi => match constOperands.toList with
    | [_] =>
      if properties.value.value = 0 then
        .useConstant (.reg (Data.RISCV.li 0))
      else .noFold
    | _ => .noFold
  | .slli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srai => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | _ => .noFold

end Veir
