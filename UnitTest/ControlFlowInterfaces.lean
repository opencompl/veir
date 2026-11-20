import Veir.Interfaces.ControlFlowInterfaces

open Veir

/-!
## Successor operands

`getOperandIndex` finds the operand of a branch that is passed to a block argument. Take

  "llvm.cond_br"(%cond, %a, %b, %c) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 2>}>

Operand 0 is the condition, `^bb1` gets `%a` (operand 1), and `^bb2` gets `%b` and `%c` (operands 2
and 3).
-/

/--
The operand of the branch above that is passed to argument `arg` of successor `successor`. Only the
segment sizes matter, so no operands are given.
-/
private def operandIndex (successor arg : Nat) : Option Nat :=
  (BranchOpInterface.getSegmentedSuccessorOperands? 1 #[1, 1, 2] #[] successor).map
    (·.getOperandIndex arg)

-- `%a`, the argument of `^bb1`, is operand 1.
#guard operandIndex 0 0 = some 1

-- `%b` and `%c`, the arguments of `^bb2`, are operands 2 and 3.
#guard operandIndex 1 0 = some 2
#guard operandIndex 1 1 = some 3
