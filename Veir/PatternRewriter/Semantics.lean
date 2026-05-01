import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
When there is no errors and no match, the input context is returned without
any changes.
-/
def LocalRewritePattern.ReturnCtxNoChanges
    (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx, pattern ctx op = some (newCtx, none) →
  ctx = newCtx

/--
`WithCreatedOps ctx₁ ctx₂` means that `ctx₂` can be constructed by creating operations
in `ctx₁` without inserting them.
-/
inductive WfIRContext.WithCreatedOps : WfIRContext OpInfo → WfIRContext OpInfo → Prop
| Nil ctx : WithCreatedOps ctx ctx
| CreatedOp
    (ctx₁ ctx₂ ctx₃ : WfIRContext OpInfo)
    (h : WithCreatedOps ctx₁ ctx₂)
    (h₂ : ∃ arg₁ arg₂ arg₃ arg₄ arg₅ arg₆ arg₈ arg₉ arg₁₀ arg₁₁,
      WfRewriter.createOp ctx₂ arg₁ arg₂ arg₃ arg₄ arg₅ arg₆ none arg₈ arg₉ arg₁₀ arg₁₁
      = some (ctx₃, newOp))
    : WithCreatedOps ctx₁ ctx₃

/--
When there is a match and no errors, the input context is returned with new operations
created.
-/
def LocalRewritePattern.ReturnCtxChangess
    (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  WfIRContext.WithCreatedOps ctx newCtx

/--
When there was a match and no errors, the returned operations are the new ones.
-/
def LocalRewritePattern.ReturnOps
  (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues,
  pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ newOp, newOp ∈ newOps ↔ newOp.InBounds newCtx.raw ∧ ¬newOp.InBounds ctx.raw

/--
We should return as many values as the number of results of the operation we
are matching.
-/
def LocalRewritePattern.ReturnValues (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op (_ : op.InBounds ctx.raw) newCtx newOps newValues,
  pattern ctx op = some (newCtx, some (newOps, newValues)) →
  newValues.size = op.getNumResults! ctx.raw

def LocalRewritePattern.PreservesSemantics
  (pattern : LocalRewritePattern OpCode)
  (_ : ReturnOps pattern) : Prop :=
  ∀ ctx (ctxDom : ctx.Dom) (op : OperationPtr) (opInBounds : op.InBounds ctx.raw),
  ∀ newCtx newOps newValues (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))),
  ∀ (state : InterpreterState), state.EquationLemmaAt ctx (InsertPoint.before op) →
  ∀ newState cf, interpretOp ctx op state = some (newState, cf) →
  ∃ newState',
    interpretOpList' newCtx newOps.toList state (by grind [ReturnOps]) = some (newState', cf) ∧
    ∀ idx (hIdx : idx < newValues.size),
      newState.getVar? (op.getResult idx) = newState'.getVar? newValues[idx]
