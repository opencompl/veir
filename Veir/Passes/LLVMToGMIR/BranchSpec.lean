module

public import Veir.Passes.LLVMToGMIR.Branches
public import Veir.Passes.InstructionSelection.Branches.Frame

public section

/-!
# What the branch translation does to a module

`LLVMBranchTranslation ctx ctx'` describes the module `ctx'` that the
translation of LLVM branches to gMIR makes of `ctx`, without reference to how
the rewriter builds it. The proof that the translation refines the module only
uses this description, and the proof about the step only has to establish it.

Every `llvm.br` and `llvm.cond_br` is replaced, in place, by one gMIR branch
with the same operands and successors. Everything else, the values and their
types included, is unchanged.
-/

namespace Veir

/-- The operation that stands for `op`, given the gMIR branch that replaces each LLVM branch. -/
abbrev translateOp (ctx : IRContext OpCode) (newBranch : OperationPtr → OperationPtr)
    (op : OperationPtr) : OperationPtr :=
  if op.IsLLVMBranch ctx then newBranch op else op

/-- `ctx'` is the branch translation of `ctx`. -/
structure LLVMBranchTranslation (ctx ctx' : WfIRContext OpCode) where
  /-- The gMIR branch that replaces an LLVM branch. -/
  newBranch : OperationPtr → OperationPtr
  /-- The blocks and regions stay. -/
  ctxSame : CtxSame ctx.raw ctx'.raw
  /-- The values and their types stay. -/
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  /-- An operation other than the two branches stays. -/
  opSame {op : OperationPtr} : op.InBounds ctx.raw → ¬ op.IsLLVMBranch ctx.raw →
    OpSame id ctx.raw ctx'.raw op
  /-- In the list of a block, each branch is replaced by its gMIR branch. -/
  opList {block : BlockPtr} (blockIn : block.InBounds ctx.raw) :
    block.opList ctx' (ctxSame.blockIn blockIn) =
      (block.opList ctx blockIn).map (translateOp ctx.raw newBranch)
  /-- The gMIR branch has no results, and the operands and successors of the branch. -/
  newBranchSpec {op : OperationPtr} : op.InBounds ctx.raw → op.IsLLVMBranch ctx.raw →
    (newBranch op).InBounds ctx'.raw ∧
    (newBranch op).getResultTypes! ctx'.raw = #[] ∧
    (newBranch op).getOperands! ctx'.raw = op.getOperands! ctx.raw ∧
    (newBranch op).getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  /-- An `llvm.br` becomes a `g_br`. -/
  newBr {op : OperationPtr} : op.InBounds ctx.raw → op.getOpType! ctx.raw = .llvm .br →
    (newBranch op).getOpType! ctx'.raw = .gmir .g_br
  /-- An `llvm.cond_br` becomes a `g_brcond` with the same operand segments. -/
  newBrCond {op : OperationPtr} : op.InBounds ctx.raw → op.getOpType! ctx.raw = .llvm .cond_br →
    (newBranch op).getOpType! ctx'.raw = .gmir .g_brcond ∧
    ((newBranch op).getProperties! ctx'.raw (OpCode.gmir .g_brcond)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes

end Veir
