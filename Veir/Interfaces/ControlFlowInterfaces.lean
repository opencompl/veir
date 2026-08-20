module

public import Veir.GlobalOpInfo

/-!
# ControlFlowInterfaces

This file provides support for querying which operands are forwarded to a successor
and mapping those operands to successor block arguments.
-/

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

namespace BranchOpInterface

/--
  Return the operands passed to `successorIndex` of a branch operation.
-/
def getSuccessorOperands?
    (branchOp : OperationPtr) (successorIndex : Nat) (raw : IRContext OpCode) :
    Option SuccessorOperands :=
  let opType := branchOp.getOpType! raw
  match opType with
  | .cf .br | .llvm .br | .riscv_cf .branch =>
    some {
      forwardedOperands := branchOp.getOperands! raw
    }
  | _ => do
    -- Determine whether this is a supported conditional branch and how many
    -- fixed operands appear before its successor operand segments.
    let fixedOperandCount ← match opType with
      | .cf .cond_br
      | .llvm .cond_br
      | .riscv_cf .beqz
      | .riscv_cf .bnez => some 1
      | .riscv_cf .beq
      | .riscv_cf .bne
      | .riscv_cf .blt
      | .riscv_cf .bge
      | .riscv_cf .bltu
      | .riscv_cf .bgeu => some 2
      | _ => none
    -- TODO: Move the operandSegmentSizes logic to the respective dialects
    -- Read the operand segment metadata from the operation's typed properties.
    let attrs := Properties.toAttrDict opType (branchOp.getProperties! raw opType)
    let some (.denseArrayAttr sizes) := attrs["operandSegmentSizes".toUTF8]? | none
    let segmentSizes := sizes.values
    -- Select the segment corresponding to the requested successor.
    let segmentIndex := fixedOperandCount + successorIndex
    let forwardedCountRaw ← segmentSizes[segmentIndex]?
    let forwardedCount := forwardedCountRaw.toNat
    -- Compute the operation operand index where this successor's forwarded values begin.
    let forwardedStart := fixedOperandCount +
      (segmentSizes.extract fixedOperandCount segmentIndex).foldl
        (init := 0) fun acc value => acc + value.toNat
    -- Return only the operands forwarded to the requested successor.
    some {
      forwardedOperands := (branchOp.getOperands! raw).extract
        forwardedStart (forwardedStart + forwardedCount)
    }

/-- Return the SSA value forwarded to a successor block argument. -/
def getSuccessorOperand?
    (branchOp : OperationPtr) (successorIndex blockArgumentIndex : Nat)
    (raw : IRContext OpCode) : Option ValuePtr :=
  getSuccessorOperands? branchOp successorIndex raw >>= fun operands =>
    operands[blockArgumentIndex]?

end BranchOpInterface

end

end Veir
