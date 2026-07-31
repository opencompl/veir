module

public import Veir.Dialects.Arith.OpInfo.Basic

public section

namespace Veir

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Arith.foldsTo (op : Arith) (properties : Arith.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .addi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .subi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .muli =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .andi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = BitVec.allOnes bw then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ori =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then
        .useConstant (.int bw (.val (BitVec.allOnes bw)))
      else .noFold
    | _ => .noFold
  | .xori =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shli =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrui =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .divsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .divui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ceildivui | .ceildivsi | .floordivsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] =>
      if c = 1 then .useOperand 0 else .noFold
    | _ => .noFold
  | .remsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 ∨ c = BitVec.allOnes bw then
        .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .remui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .maxsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then .useOperand 0
      else if c = BitVec.intMax bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then .useOperand 0
      else if c = BitVec.intMin bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .maxui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then .useOperand 0
      else if c = 0 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .cmpi =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then .useOperand 0
      else if properties.predicate = .eq ∧ c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .select => Fold.selectFoldsTo resultTypes constOperands
  | _ => .noFold

end Veir
