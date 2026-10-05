module

public import Veir.Rewriter.InsertPoint
public import Veir.Dominance.Basic
public import Veir.Dominance.Lemmas
public import Veir.Interfaces.RegionKindInterfaces

import all Veir.Dominance.Basic

/-!
  # Dominance

  This file is a placeholder for the dominance relation between IR constructs.
  It currently only contains axioms, and will be filled in with actual definitions and proofs
  in the future.

  This formalization assumes that all regions are SSACFG regions, so it particular it doesn't
  support graph regions.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}

/--
  The dominance relation between an operation and an insertion point.
-/
axiom OperationPtr.dominatesIp (op : OperationPtr) (ip : InsertPoint) (ctx : WfIRContext OpInfo) : Prop

/--
  The dominance relation between a value and an insertion point.
-/
axiom ValuePtr.dominatesIp (val : ValuePtr) (ip : InsertPoint) (ctx : WfIRContext OpInfo) : Prop

/-!
## Lemmas about Dominance
-/

/--
An operation `op₁` dominates the program point after a given operation `op₂` if it
either dominates the `op₂`, or is `op₂`.
-/
axiom OperationPtr.dominatesIp_iff :
    op₁.dominatesIp (InsertPoint.after op₂ ctx.raw block op₂HasParent op₂InBounds) ctx ↔
    op₁.Dominates op₂ ctx

/--
An operation `op₁` dominates the program point before `op₂` if it properly dominates `op₂`.
-/
@[simp]
axiom OperationPtr.dominatesIp_before :
  op₁.dominatesIp (.before op₂) ctx ↔ op₁.ProperlyDominates op₂ ctx true

grind_pattern OperationPtr.dominatesIp_before => op₁.dominatesIp (.before op₂) ctx

/--
A value dominating the program point before an operation `op₁` also dominates the program
point before any operation `op₂` properly dominated by `op₁`.
-/
axiom ValuePtr.dominatesIp_before_of_properlyDominates {value : ValuePtr} :
  value.dominatesIp (InsertPoint.before op₁) ctx → op₁.ProperlyDominates op₂ ctx true →
  value.dominatesIp (InsertPoint.before op₂) ctx

/-!
## Programs Satisfying Dominance Invariants

This section defines `WfIRContext.DomAll`, the global dominance invariant for every in-bounds
operation.
-/

/--
  A predicate that states that the values in the IR context are used in operations that
  are dominated by the operation or block that defines them.
-/
def WfIRContext.DomAll (ctx : WfIRContext OpInfo) : Prop :=
  ∀ {op : OperationPtr} (_opInBounds : op.InBounds ctx.raw) {value : ValuePtr},
  value ∈ op.getOperands! ctx.raw →
  value.dominatesIp (InsertPoint.before op) ctx

/--
Operands of an operation are not results of dominated operations.
-/
axiom IRContext.DomAll.value_not_in_results_of_forall_in_operands_of_dominates (ctxDom : ctx.DomAll) :
    op₁.Dominates op₂ ctx →
    ∀ (value : ValuePtr), value ∈ op₁.getOperands! ctx.raw →
    value ∉ op₂.getResults! ctx.raw

/-- In a well-dominated IR context, any value that is an operand of an operation `op` is
dominating the program point before `op`. -/
@[grind →]
theorem WfIRContext.DomAll.operand_dominates_op (ctxDom : ctx.DomAll)
    (opInBounds : op.InBounds ctx.raw) :
    value ∈ op.getOperands! ctx.raw →
    value.dominatesIp (InsertPoint.before op) ctx := by
  grind [WfIRContext.DomAll]

/-- In a well-dominated IR context, a value dominates the program point after an operation iff
it dominates the program point before the operation, or it is a result of the operation. -/
axiom WfIRContext.DomAll.value_dominatesIp_after_iff (ctxDom : ctx.DomAll) :
  value.dominatesIp (InsertPoint.after op ctx.raw block blockIsParent opInBounds) ctx ↔
  value.dominatesIp (InsertPoint.before op) ctx ∨ value ∈ op.getResults! ctx.raw

/-- A value dominating the entry of a successor block either already dominates the predecessor's
end, or it is one of the successor's own block arguments. -/
axiom WfIRContext.DomAll.value_dominatesIp_successor_entry (ctxDom : ctx.DomAll)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    value.dominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    value.dominatesIp (InsertPoint.atEnd block) ctx ∨
      value ∈ succ.getArguments! ctx.raw

/-- An operation dominating the entry of a successor already dominates the predecessor's end. -/
axiom WfIRContext.DomAll.op_dominatesIp_successor_entry (ctxDom : ctx.DomAll)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    op.dominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    op.dominatesIp (InsertPoint.atEnd block) ctx

/-- An argument of a block dominates the block's start. -/
axiom WfIRContext.DomAll.blockArgument_dominatesIp_entry (ctxDom : ctx.DomAll)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx

/-- An argument of an SSACFG block with rooted, reachable ancestry cannot dominate a program point
that dominates the block start. -/
axiom WfIRContext.Dom.blockArgument_not_dominatesIp_before_of_dominatesIp_firstOp
    (ctxDom : ctx.DomAll) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (ssa : region.hasSSADominance ctx = true)
    (rooted : ∃ root : IRNode, root.Ancestor (.block block) ctx ∧ root.parent! ctx = none)
    (reachable : ∀ ancestor region, (IRNode.block ancestor).Ancestor (.block block) ctx →
      (ancestor.get! ctx.raw).parent = some region → region.hasSSADominance ctx = true →
      ancestor.LocallyReachable region ctx)
    (opDom : op.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    ¬ value.dominatesIp (InsertPoint.before op) ctx
