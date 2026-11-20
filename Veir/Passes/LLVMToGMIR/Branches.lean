module

public import Veir.Pass

namespace Veir

/-!
  # Translating LLVM branches to gMIR

  The branch step of the `llvm-to-gmir` pass replaces every `llvm.br` by a
  `gmir.g_br` and every `llvm.cond_br` by a `gmir.g_brcond`, with the same
  operands and successors, as LLVM's `IRTranslator::translateBr`. It is written
  with folds over lists, so that it can be reasoned about.

  A `g_brcond` takes its first successor when its condition is not zero, an
  `llvm.cond_br` when its `i1` condition is one, so they agree on an `i1`.
-/

/-- `op` is one of the two LLVM branches that the step replaces. -/
public abbrev OperationPtr.IsLLVMBranch (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  op.getOpType! ctx = .llvm .br ∨ op.getOpType! ctx = .llvm .cond_br

/--
  The gMIR branch that replaces the LLVM branch `op`, created in front of it, with
  the operands and successors of `op`.
-/
public def createGMIRBranch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  let operands := op.getOperands! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  if op.getOpType! ctx.raw = .llvm .br then
    WfRewriter.createOp! ctx GMIR.g_br #[] operands successors #[] () (some (.before op))
  else
    let props : LLVMCondBrProperties := op.getProperties! ctx.raw (OpCode.llvm .cond_br)
    WfRewriter.createOp! ctx GMIR.g_brcond #[] operands successors #[]
      (GMIRBrCondProperties.mk props.operandSegmentSizes) (some (.before op))

/-- Replace `op` by a gMIR branch if it is an LLVM branch, and leave any other operation alone. -/
public def convertLLVMBranch (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (WfIRContext OpCode) := do
  if ¬ op.IsLLVMBranch ctx.raw then
    return ctx
  if op.getNumResults! ctx.raw ≠ 0 ∨ op.getNumRegions! ctx.raw ≠ 0 then
    throw "llvm-to-gmir: a branch has results or regions"
  let some (ctx', _) := createGMIRBranch ctx op
    | throw "llvm-to-gmir: cannot create a gMIR branch"
  return WfRewriter.eraseOp! ctx' op

/--
  Replace every LLVM branch of the module by a gMIR branch. The operations to
  visit are fixed up front, so the branches the step creates are not visited.
-/
public def convertLLVMBranches (ctx : WfIRContext OpCode) : Except String (WfIRContext OpCode) :=
  ctx.raw.operations.keys.foldlM convertLLVMBranch ctx

end Veir
