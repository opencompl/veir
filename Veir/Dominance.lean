module

public import Veir.IR.WellFormed
public import Veir.IR.OpInfo
public import Veir.Rewriter.InsertPoint
public import Veir.Dominance.Block
public import Veir.Dominance.Path
public import Veir.Dominance.Projection
public import Veir.Dominance.InsertPoint
public import Veir.Dominance.Operation
public import Veir.Dominance.Path
public import Veir.Dominance.Block
public import Veir.Dominance.InsertPoint
public import Veir.Dominance.Operation
public import Veir.Dominance.Value

/-!
  # Propositional dominance

  Operation dominance is defined propositionally in `Veir.Dominance.Operation`,
  including SSACFG and graph-region semantics and nested operation hierarchy.
  `Veir.Dominance.Value` defines operation-result and block-argument
  availability at insertion points.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}

/-!
## Definition of Dominance
-/

/-!
## Programs Satisfying Dominance Invariants

This section defines `IRContext.Dom`, which ensure that the values in an `IRContext` respects
SSA dominance.
-/

/--
The operands of `op` do not depend on an operation dominated by `op`.

This is the acyclicity part of SSA use ordering. It is intentionally separate
from `WfIRContext.Dom`: graph regions allow cyclic and self uses, so ordinary
dominance checking alone cannot imply this property there.
-/
def OperationPtr.OperandsAreDominanceAcyclic
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  ∀ {value : ValuePtr} {definingOp : OperationPtr},
    value ∈ op.getOperands! ctx.raw →
    value.getDefiningOp! ctx.raw = some definingOp →
    ¬ op.Dominates definingOp ctx

/--
Operand uses of every operation dominating `target` are well-founded for
interpreting those operations before `target`.

Besides excluding operation-result cycles, this records that every operand of
a dominator is available at `target`. The latter cannot be recovered from
operation dominance alone in graph regions or across unreachable blocks.
-/
structure OperationPtr.DominatingOperandUsesAreWellFounded
    (target : OperationPtr) (ctx : WfIRContext OpInfo) : Prop where
  acyclic : ∀ source : OperationPtr,
    source.Dominates target ctx → source.OperandsAreDominanceAcyclic ctx
  operandDominatesTarget : ∀ {source : OperationPtr} {value : ValuePtr},
    source.Dominates target ctx →
    value ∈ source.getOperands! ctx.raw →
    value.DominatesIp (InsertPoint.before target) ctx

/--
An operation does not use block arguments whose block entry it dominates.

This is the block-argument counterpart of `OperandsAreDominanceAcyclic`.
It is intentionally explicit: graph regions and unreachable SSACFG blocks
make dominance alone too weak to rule out such cyclic uses.
-/
def OperationPtr.BlockArgumentUsesAreDominanceAcyclic
    (op : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  ∀ {block : BlockPtr} {value : ValuePtr},
    op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx →
    value ∈ block.getArguments! ctx.raw →
    value ∉ op.getOperands! ctx.raw

namespace OperationPtr.DominatingOperandUsesAreWellFounded

/-- Obtain operand acyclicity for a particular dominator. -/
theorem of_dominates
    {target source : OperationPtr}
    (wellFounded : target.DominatingOperandUsesAreWellFounded ctx)
    (dominance : source.Dominates target ctx) :
    source.OperandsAreDominanceAcyclic ctx :=
  wellFounded.acyclic source dominance

/-- The target operation itself has acyclic operands. -/
theorem self
    {target : OperationPtr}
    (wellFounded : target.DominatingOperandUsesAreWellFounded ctx) :
    target.OperandsAreDominanceAcyclic ctx :=
  wellFounded.of_dominates OperationPtr.dominates_refl

/-- An operand of a target dominator is available before the target. -/
theorem operand_dominates
    {target source : OperationPtr} {value : ValuePtr}
    (wellFounded : target.DominatingOperandUsesAreWellFounded ctx)
    (dominance : source.Dominates target ctx)
    (operandMem : value ∈ source.getOperands! ctx.raw) :
    value.DominatesIp (InsertPoint.before target) ctx :=
  wellFounded.operandDominatesTarget dominance operandMem

end OperationPtr.DominatingOperandUsesAreWellFounded

/--
  A predicate that states that the values in the IR context are used in operations that
  are dominated by the operation or block that defines them.
-/
def WfIRContext.Dom (ctx : WfIRContext OpInfo) : Prop :=
  ∀ {op : OperationPtr} (_opInBounds : op.InBounds ctx.raw) {value : ValuePtr},
  op.ReachableFromEntry ctx →
  value ∈ op.getOperands! ctx.raw →
  value.DominatesIp (InsertPoint.before op) ctx

/--
Operands of an operation are not results of dominated operations.
-/
theorem IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
    (_ctxDom : ctx.Dom)
    (op₁Acyclic : op₁.OperandsAreDominanceAcyclic ctx) :
    op₁.Dominates op₂ ctx →
    ∀ (value : ValuePtr), value ∈ op₁.getOperands! ctx.raw →
    value ∉ op₂.getResults! ctx.raw := by
  intro opDominance value operandMem resultMem
  have definingOp : value.getDefiningOp! ctx.raw = some op₂ :=
    ValuePtr.getDefiningOp!_eq_some_of_mem_getResults resultMem
  exact op₁Acyclic operandMem definingOp opDominance

/--
If a value is defined by `op₁` and used by an `op₂` reachable from entry, then
`op₁` dominates `op₂`. Graph regions may permit `op₁ = op₂`.
-/
theorem OperationPtr.dominates_of_getDefiningOp!_of_mem_getOperands!
    (ctxDom : ctx.Dom)
    (op₂InBounds : op₂.InBounds ctx.raw)
    (op₂Reachable : op₂.ReachableFromEntry ctx) :
  value.getDefiningOp! ctx.raw = some op₁ →
  value ∈ op₂.getOperands! ctx.raw →
  op₁.Dominates op₂ ctx := by
  intro definingOp operandMem
  obtain ⟨result, rfl, resultOwner⟩ :=
    ValuePtr.getDefiningOp!_eq_some_iff.mp definingOp
  have resultDominance :=
    ctxDom op₂InBounds op₂Reachable operandMem
  exact OpResultPtr.owner_dominates_of_dominatesIp_before
    resultOwner resultDominance

/--
Strict defining-operation dominance follows when the use operation's operands
are dominance-acyclic. This premise rules out graph-region self uses.
-/
theorem OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!
    (ctxDom : ctx.Dom)
    (op₂InBounds : op₂.InBounds ctx.raw)
    (op₂Reachable : op₂.ReachableFromEntry ctx)
    (op₂Acyclic : op₂.OperandsAreDominanceAcyclic ctx) :
  value.getDefiningOp! ctx.raw = some op₁ →
  value ∈ op₂.getOperands! ctx.raw →
  op₁.StrictlyDominates op₂ ctx := by
  intro definingOp operandMem
  have ordinaryDominance :=
    OperationPtr.dominates_of_getDefiningOp!_of_mem_getOperands!
      ctxDom op₂InBounds op₂Reachable definingOp operandMem
  refine ⟨ordinaryDominance, ?_⟩
  intro definingEq
  subst op₁
  exact op₂Acyclic operandMem definingOp OperationPtr.dominates_refl

/-- In a well-dominated IR context, any value that is an operand of an operation `op` is
dominating the program point before `op`. -/
@[grind →]
theorem WfIRContext.Dom.operand_dominates_op (ctxDom : ctx.Dom)
    (opInBounds : op.InBounds ctx.raw)
    (opReachable : op.ReachableFromEntry ctx) :
    value ∈ op.getOperands! ctx.raw →
    value.DominatesIp (InsertPoint.before op) ctx := by
  grind [WfIRContext.Dom]

/-- In a well-dominated IR context, a value dominates the program point after an operation iff
it dominates the program point before the operation, or it is a result of the operation. -/
theorem WfIRContext.Dom.value_dominatesIp_after_iff (_ctxDom : ctx.Dom)
    {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region) :
  value.DominatesIp (InsertPoint.after op ctx.raw block blockIsParent opInBounds) ctx ↔
  value.DominatesIp (InsertPoint.before op) ctx ∨ value ∈ op.getResults! ctx.raw := by
  cases value with
  | opResult result =>
      exact OpResultPtr.dominatesIp_after_iff_before_or_mem
        blockIsParent blockParent opInBounds
  | blockArgument argument =>
      have notMem :
          ValuePtr.blockArgument argument ∉ op.getResults! ctx.raw := by
        intro argumentMem
        obtain ⟨index, indexInBounds, resultEq⟩ :=
          OperationPtr.getResults!.mem_iff_exists_index.mp argumentMem
        cases resultEq
      simp only [ValuePtr.DominatesIp, BlockArgumentPtr.DominatesIp]
      rw [BlockPtr.dominatesIp_after_iff_before blockIsParent opInBounds]
      simp [notMem]

/-- A value dominating the entry of a successor block either already dominates the predecessor's
end, or it is one of the successor's own block arguments. -/
theorem WfIRContext.Dom.value_dominatesIp_successor_entry
    {ctx : WfIRContext OpCode} (_ctxDom : ctx.Dom)
    (ctxVerified : ctx.Verified)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    value.DominatesIp (InsertPoint.atEnd block) ctx ∨
      value ∈ succ.getArguments! ctx.raw := by
  intro successorDominance
  cases value with
  | opResult result =>
      left
      exact OpResultPtr.dominatesIp_predecessor_end_of_successor_entry
        ctxVerified blockParent blockInBounds hsucc successorDominance
  | blockArgument argument =>
      exact BlockArgumentPtr.dominatesIp_predecessor_end_or_mem_of_successor_entry
        ctxVerified blockParent blockInBounds hsucc successorDominance

/-- An argument of a block dominates the block's start. -/
theorem WfIRContext.Dom.blockArgument_dominatesIp_entry (_ctxDom : ctx.Dom)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx := by
  obtain ⟨index, indexInBounds, argumentEq⟩ :=
    BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
  have argumentOwner :
      ((block.getArgument index).get! ctx.raw).owner = block :=
    (ctx.wellFormed.blocks block blockInBounds).argument_owners
      index indexInBounds
  have argumentInBounds : (block.getArgument index).InBounds ctx.raw := by
    grind [BlockArgumentPtr.inBounds_def]
  rw [← argumentEq]
  change (block.getArgument index).DominatesIp
    (InsertPoint.atStart! block ctx.raw) ctx
  exact BlockArgumentPtr.dominatesIp_atStart
    argumentInBounds argumentOwner blockParent blockInBounds
