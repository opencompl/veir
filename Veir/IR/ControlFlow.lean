module

public import Veir.IR.Basic
public import Veir.RuntimeValue.Basic

namespace Veir

public section

/-- The SSA values forwarded from a branch operation to one of its successors. -/
structure SuccessorOperands where
  /-- The SSA values forwarded to the successor. -/
  forwardedOperands : Array ValuePtr
deriving Inhabited, Repr, DecidableEq

instance : GetElem SuccessorOperands Nat ValuePtr
    (fun operands blockArgumentIndex => blockArgumentIndex < operands.forwardedOperands.size) where
  getElem := fun operands blockArgumentIndex h => operands.forwardedOperands[blockArgumentIndex]'h

instance : GetElem? SuccessorOperands Nat ValuePtr
    (fun operands blockArgumentIndex => blockArgumentIndex < operands.forwardedOperands.size) where
  getElem? := fun operands blockArgumentIndex => operands.forwardedOperands[blockArgumentIndex]?

/-- Information exposed by operations that branch to successor blocks. -/
structure BranchOpInterface (Properties : Type) where
  /-- Return the operands passed to the indexed successor. -/
  getSuccessorOperandsImpl? :
    Properties → Array ValuePtr → Nat → Option SuccessorOperands
  /-- Return the successor selected by the known constant operands. -/
  getSuccessorForOperandsImpl? :
    Properties → Array (Option RuntimeValue) → Array BlockPtr → Option BlockPtr :=
      fun _ _ _ => none

namespace BranchOpInterface

/-- Return the true or false successor of a conditional branch. -/
def getConditionalSuccessor?
    (successors : Array BlockPtr) (condition : Bool) : Option BlockPtr :=
  if condition then successors[0]? else successors[1]?

/--
Return the operands in the successor segment of an operation whose fixed operands
precede one operand segment per successor.
-/
def getSegmentedSuccessorOperands?
    (fixedOperandCount : Nat) (segmentSizes : Array Int) (operands : Array ValuePtr)
    (successorIndex : Nat) : Option SuccessorOperands := do
  let segmentIndex := fixedOperandCount + successorIndex
  let forwardedCountRaw ← segmentSizes[segmentIndex]?
  let forwardedCount := forwardedCountRaw.toNat
  let forwardedStart := fixedOperandCount +
    (segmentSizes.extract fixedOperandCount segmentIndex).foldl
      (init := 0) fun acc value => acc + value.toNat
  some {
    forwardedOperands := operands.extract forwardedStart (forwardedStart + forwardedCount)
  }

end BranchOpInterface

end

end Veir
