module

public import Veir.Rewriter.SetOperands
public import Veir.Interfaces.ControlFlowInterfaces

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

private def WfRewriter.updateSuccessorOperands (ctx : WfIRContext OpInfo)
    (branch : OperationPtr) (successorIndex : Nat) (values : Array ValuePtr)
    (append : Bool) : Except String (WfIRContext OpInfo) := do
  unless branch.InBounds ctx.raw do
    throw "branch operation is out of bounds"
  unless successorIndex < branch.getNumSuccessors! ctx.raw do
    throw "successor index is out of bounds"
  let opType := branch.getOpType! ctx.raw
  let some interface := HasOpInfo.branchOpInterface? opType
    | throw "operation does not implement the branch interface"
  let some range := interface.getSuccessorOperandsMutableImpl?
      (branch.getProperties! ctx.raw opType) (branch.getNumOperands! ctx.raw) successorIndex
    | throw "successor operand mutation is unsupported"
  let start := if append then range.start + range.length else range.start
  let length := if append then 0 else range.length
  let newLength := if append then range.length + values.size else values.size
  let ctx ← WfRewriter.setOperandRange ctx branch start length values
  return WfRewriter.setProperties! ctx branch opType (range.setLength newLength)

/--
Replace the operands forwarded along one successor edge, updating operand segment
sizes through the dialect's mutable range description. The operation's identity,
successors, attributes, and unrelated properties are preserved.

Requires a verified operand layout. The successor is identified by edge index,
including when several edges target the same block. Destination block argument
counts may temporarily differ while a transformation updates incoming edges.
-/
def WfRewriter.setSuccessorOperands (ctx : WfIRContext OpInfo)
    (branch : OperationPtr) (successorIndex : Nat) (values : Array ValuePtr) :
    Except String (WfIRContext OpInfo) :=
  WfRewriter.updateSuccessorOperands ctx branch successorIndex values false

/-- Append forwarded operands to one successor edge and update its segment sizes. -/
def WfRewriter.appendSuccessorOperands (ctx : WfIRContext OpInfo)
    (branch : OperationPtr) (successorIndex : Nat) (values : Array ValuePtr) :
    Except String (WfIRContext OpInfo) :=
  WfRewriter.updateSuccessorOperands ctx branch successorIndex values true

end Veir
