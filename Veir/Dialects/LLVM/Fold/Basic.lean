module

public import Veir.Dialects.LLVM.OpInfo.Basic

public section

namespace Veir

/--
  Fold table for `llvm` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Llvm.foldsTo (op : Llvm) (properties : Llvm.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .add =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sub =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .mul =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .and =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = BitVec.allOnes bw then .useOperand 0
      else .noFold
    | _ => .noFold
  | .or =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then
        .useConstant (.int bw (.val (BitVec.allOnes bw)))
      else .noFold
    | _ => .noFold
  | .xor =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shl =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .lshr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .ashr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .sdiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .udiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .srem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 ∨ c = BitVec.allOnes bw then
        .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .urem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .intr__smax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then .useOperand 0
      else if c = BitVec.intMax bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__smin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then .useOperand 0
      else if c = BitVec.intMin bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__umax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__umin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then .useOperand 0
      else if c = 0 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .icmp =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then .useOperand 0
      else if properties.predicate = .eq ∧ c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .select => Fold.selectFoldsTo resultTypes constOperands
  | _ => .noFold

end Veir
