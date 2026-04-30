module

public import Veir.IR.WellFormed
public import Veir.IR.OpInfo
public import Veir.Rewriter.InsertPoint

/-!
  # Dominance

  This file is a placeholder for the dominance relation between IR constructs.
  It currently only contains axioms, and will be filled in with actual definitions and proofs
  in the future.
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
axiom OperationPtr.dominatesIp_before :
  op₁.dominatesIp (.before op₂) ctx ↔ op₁.strictlyDominates op₂ ctx

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
axiom WfIRContext.Dom (ctx : WfIRContext OpInfo) : Prop


/--
Operands of an operation are not results of dominated operations.
-/
axiom IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates (ctxDom : ctx.Dom) :
    op₁.dominates op₂ ctx →
    ∀ (value : ValuePtr), value ∈ op₁.getOperands! ctx.raw →
    value ∉ op₂.getResults! ctx.raw
