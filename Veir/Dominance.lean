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

  `WfIRContext.verifyDominance` (in `Veir/Verifier.lean`) is the executable decision
  procedure for this predicate: it visits every in-bounds operation and every operand,
  and for each checks `value.dominatesIp (InsertPoint.before op) ctx` via the dominance
  analysis. A successful run is intended to witness exactly `ctx.Dom`; the checker is
  written so that each step matches a clause of this definition. (`ctx.Dom` assumes
  SSACFG regions, and the checker restricts itself to SSACFG, reachable blocks
  accordingly.)
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
