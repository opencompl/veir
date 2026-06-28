module

public import Veir.IR.WellFormed
public import Veir.IR.OpInfo
public import Veir.Rewriter.InsertPoint

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

/-!
## Definition of Dominance
-/

/--
  The dominance relation between operations.
  An operation `op` dominates itself.
-/
axiom OperationPtr.dominates (op₁ op₂ : OperationPtr) (ctx : WfIRContext OpInfo) : Prop

/--
  The strict dominance relation between operations.
  An operation `op` does not strictly dominate itself.
-/
def OperationPtr.strictlyDominates (op₁ op₂ : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  op₁.dominates op₂ ctx ∧ op₁ ≠ op₂

/--
  An operation `op₁` strictly dominates an operation `op₂` if it dominates it
  and the operations are not equal.
-/
theorem OperationPtr.strictlyDominates_def :
    op₁.strictlyDominates op₂ ctx ↔ op₁.dominates op₂ ctx ∧ op₁ ≠ op₂ := by
  grind [strictlyDominates]

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
An operation `op₁` dominates an operation `op₂` if it strictly dominates it.
-/
theorem OperationPtr.dominates_of_strictlyDominates :
    op₁.strictlyDominates op₂ ctx → op₁.dominates op₂ ctx := by
  grind [strictlyDominates]

/--
An operation dominates itself.
-/
@[grind .]
axiom OperationPtr.dominates_refl : op.dominates op ctx

/--
An operation `op₁` dominates an operation `op₂` if and only if
`op₁` stricly dominates `op₂` or if `op₁` is `op₂`.
-/
theorem OperationPtr.dominates_iff_strictlyDominates_or_eq :
    op₁.dominates op₂ ctx ↔ op₁.strictlyDominates op₂ ctx ∨ op₁ = op₂ := by
  grind [OperationPtr.strictlyDominates]

/--
An operation `op₁` dominates the program point after a given operation `op₂` if it
either dominates the `op₂`, or is `op₂`.
-/
axiom OperationPtr.dominatesIp_iff :
    op₁.dominatesIp (InsertPoint.after op₂ ctx.raw block op₂HasParent op₂InBounds) ctx ↔
    op₁.dominates op₂ ctx

/--
An operation `op₁` dominates the program point before `op₂` if it strictly dominates `op₂`.
-/
@[simp]
axiom OperationPtr.dominatesIp_before :
  op₁.dominatesIp (.before op₂) ctx ↔ op₁.strictlyDominates op₂ ctx

grind_pattern OperationPtr.dominatesIp_before => op₁.dominatesIp (.before op₂) ctx

/--
Strict dominance between operations is transitive.
-/
axiom OperationPtr.strictlyDominates_trans {op₃ : OperationPtr} :
  op₁.strictlyDominates op₂ ctx → op₂.strictlyDominates op₃ ctx →
  op₁.strictlyDominates op₃ ctx

/--
A value dominating the program point before an operation `op₁` also dominates the program
point before any operation `op₂` strictly dominated by `op₁`.
-/
axiom ValuePtr.dominatesIp_before_of_strictlyDominates {value : ValuePtr} :
  value.dominatesIp (InsertPoint.before op₁) ctx → op₁.strictlyDominates op₂ ctx →
  value.dominatesIp (InsertPoint.before op₂) ctx

/--
If an operation `op₁` dominates an operation `op₂`, it dominates the operation after `op₂`,
if it exists.
-/
axiom OperationPtr.dominates_next :
  op₁.dominates op₂ ctx →
  (op₂.get! ctx.raw).next = some op₂Next →
  op₁.dominates op₂Next ctx

/-!
## Programs Satisfying Dominance Invariants

This section defines `IRContext.Dom`, which ensure that the values in an `IRContext` respects
SSA dominance.
-/

/--
  A predicate that states that the values in the IR context are used in operations that
  are dominated by the operation or block that defines them.
-/
def WfIRContext.Dom (ctx : WfIRContext OpInfo) : Prop :=
  ∀ {op : OperationPtr} (_opInBounds : op.InBounds ctx.raw) {value : ValuePtr},
  value ∈ op.getOperands! ctx.raw →
  value.dominatesIp (InsertPoint.before op) ctx

/--
Operands of an operation are not results of dominated operations.
-/
axiom IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates (ctxDom : ctx.Dom) :
    op₁.dominates op₂ ctx →
    ∀ (value : ValuePtr), value ∈ op₁.getOperands! ctx.raw →
    value ∉ op₂.getResults! ctx.raw

/--
If a value is being defined by an operation `op₁` and being used as an operand of an
operation `op₂`, then `op₁` strictly dominates `op₂`.
-/
axiom OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! (ctxDom : ctx.Dom) :
  value.getDefiningOp! ctx.raw = some op₁ →
  value ∈ op₂.getOperands! ctx.raw →
  op₁.strictlyDominates op₂ ctx

grind_pattern OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! =>
  ctx.Dom, value.getDefiningOp! ctx.raw, some op₂, op₁.getOperands! ctx.raw

/-- In a well-dominated IR context, any value that is an operand of an operation `op` is
dominating the program point before `op`. -/
@[grind →]
theorem WfIRContext.Dom.operand_dominates_op (ctxDom : ctx.Dom)
    (opInBounds : op.InBounds ctx.raw) :
    value ∈ op.getOperands! ctx.raw →
    value.dominatesIp (InsertPoint.before op) ctx := by
  grind [WfIRContext.Dom]

/-- In a well-dominated IR context, a value dominates the program point after an operation iff
it dominates the program point before the operation, or it is a result of the operation. -/
axiom WfIRContext.Dom.value_dominatesIp_after_iff (ctxDom : ctx.Dom) :
  value.dominatesIp (InsertPoint.after op ctx.raw block blockIsParent opInBounds) ctx ↔
  value.dominatesIp (InsertPoint.before op) ctx ∨ value ∈ op.getResults! ctx.raw

/-- A value dominating the entry of a successor block either already dominates the predecessor's
end, or it is one of the successor's own block arguments. -/
axiom WfIRContext.Dom.value_dominatesIp_successor_entry (ctxDom : ctx.Dom)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    value.dominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    value.dominatesIp (InsertPoint.atEnd block) ctx ∨
      value ∈ succ.getArguments! ctx.raw

/-- An operation dominating the entry of a successor already dominates the predecessor's end. -/
axiom WfIRContext.Dom.op_dominatesIp_successor_entry (ctxDom : ctx.Dom)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    op.dominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    op.dominatesIp (InsertPoint.atEnd block) ctx

/-- An argument of a block dominates the block's start. -/
axiom WfIRContext.Dom.blockArgument_dominatesIp_entry (ctxDom : ctx.Dom)
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx

/-- An argument of a block cannot dominate a program point that dominates the block start. -/
axiom WfIRContext.Dom.blockArgument_not_dominatesIp_before_of_dominatesIp_firstOp
    (ctxDom : ctx.Dom) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    (opDom : op.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    ¬ value.dominatesIp (InsertPoint.before op) ctx

/-- A block argument dominates the end of its own block: it is in scope throughout the block body. -/
axiom WfIRContext.Dom.blockArgument_dominatesIp_atEnd
    (ctxDom : ctx.Dom) {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.dominatesIp (InsertPoint.atEnd block) ctx

/-- A result of an operation in a block body does not dominate that block's entry (the SSA
property: results are defined strictly inside the block, not before it). -/
axiom WfIRContext.Dom.opResult_not_dominatesIp_atStart!
    (ctxDom : ctx.Dom) {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (opInBlock : op ∈ block.operationList ctx.raw ctx.wellFormed blockIn)
    {r : ValuePtr} (rResult : r ∈ op.getResults! ctx.raw) :
    ¬ r.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx

/-!
## Block-level dominance

Dominance between blocks (the entry of `b₁` dominates every point of `b₂`). Used to discharge the
cross-block antisymmetry argument in the pattern-rewriter soundness proof: a value forwarded by a
rewrite cannot become an argument of a *different* block.
-/

variable {b₁ b₂ block bl : BlockPtr}

/-- The dominance relation between two blocks: `b₁` dominates `b₂` when `b₁`'s entry dominates every
program point of `b₂`. A block dominates itself. -/
axiom BlockPtr.dominates (b₁ b₂ : BlockPtr) (ctx : WfIRContext OpInfo) : Prop

/-- Block dominance is antisymmetric: two blocks that dominate each other are equal. -/
axiom BlockPtr.dominates_antisymm :
    b₁.dominates b₂ ctx → b₂.dominates b₁ ctx → b₁ = b₂

/-- If a result `r` of an operation `op` living in `block` dominates the entry of a block `bl`, then
`block` dominates `bl` (the definition site of `r` is in `block`, and `r` reaches all of `bl`). -/
axiom WfIRContext.Dom.block_dominates_of_opResult_dominatesIp_atStart!
    (ctxDom : ctx.Dom) {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (blockIn : block.InBounds ctx.raw) (blIn : bl.InBounds ctx.raw)
    (opInBlock : op ∈ block.operationList ctx.raw ctx.wellFormed blockIn)
    {r : ValuePtr} (rResult : r ∈ op.getResults! ctx.raw)
    (rDom : r.dominatesIp (InsertPoint.atStart! bl ctx.raw) ctx) :
    block.dominates bl ctx

/-- If an argument `w` of a block `bl` dominates a program point inside `block` (the end of a list of
`block`'s operations, started from `block`'s entry), then `bl` dominates `block`: `w` is in scope
from `bl`'s entry, so `bl`'s entry dominates that point, hence all of `block`. -/
axiom WfIRContext.Dom.block_dominates_of_arg_dominatesIp_afterLast
    (ctxDom : ctx.Dom) (blIn : bl.InBounds ctx.raw) (blockIn : block.InBounds ctx.raw)
    {w : ValuePtr} (wArg : w ∈ bl.getArguments! ctx.raw)
    {ops : List OperationPtr}
    (hops : ∀ o ∈ ops, o ∈ block.operationList ctx.raw ctx.wellFormed blockIn)
    (wDom : w.dominatesIp (InsertPoint.afterLast ops ctx.raw (.atStart! block ctx.raw)) ctx) :
    bl.dominates block ctx
