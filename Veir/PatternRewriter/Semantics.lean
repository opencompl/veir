import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Asserts that the pattern returns the input context whenever there are no errors and no match.
-/
def LocalRewritePattern.ReturnsCtxNoChanges (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx, pattern ctx op = some (newCtx, none) → ctx = newCtx

/--
`WithCreatedOps ctx₁ ctx₂` asserts that `ctx₂` can be constructed by creating new operations
in `ctx₁` without inserting them in a block.
-/
inductive WfIRContext.WithCreatedOps : WfIRContext OpInfo → WfIRContext OpInfo → Prop
| Nil ctx : WithCreatedOps ctx ctx
| CreatedOp
    (ctx₁ ctx₂ ctx₃ : WfIRContext OpInfo)
    (h : WithCreatedOps ctx₁ ctx₂)
    (h₂ : ∃ opType resultTypes operands successors regions properties h₁ h₂ h₃ h₄,
      WfRewriter.createOp ctx₂ opType resultTypes operands successors
        regions properties none h₁ h₂ h₃ h₄ = some (ctx₃, newOp))
    : WithCreatedOps ctx₁ ctx₃

@[grind .]
theorem WfIRContext.WithCreatedOps.inBounds_mono {ctx₁ ctx₂ : WfIRContext OpInfo}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) :
    ∀ ptr : GenericPtr, ptr.InBounds ctx₁.raw → ptr.InBounds ctx₂.raw := by
  intro ptr inBounds
  induction h <;> grind

@[local grind =>]
theorem WfIRContext.WithCreatedOps.preserves_VariableState_conforms {ctx₁ ctx₂ : WfIRContext OpInfo}
    (state : InterpreterState ctx₁) :
    WfIRContext.WithCreatedOps ctx₁ ctx₂ →
    VariableState.ValuesConform state.variables.variables ctx₂ := by
  intro h
  induction h
  case Nil => grind [cases InterpreterState, cases VariableState]
  case CreatedOp ctx₁ ctx₂ ctx₃ _ hctx₃ hi =>
    simp only [VariableState.ValuesConform] at hi ⊢
    grind [cases InterpreterState, cases VariableState]

@[local grind →]
theorem WfIRContext.WithCreatedOps.preserves_VariableState_inBounds {ctx₁ ctx₂ : WfIRContext OpInfo}
    (state : InterpreterState ctx₁) :
    WfIRContext.WithCreatedOps ctx₁ ctx₂ →
    ∀ (val : ValuePtr), val ∈ state.variables.variables → val.InBounds ctx₂.raw := by
  grind [cases InterpreterState, cases VariableState]

/--
When there is a match and no errors, the output context is only modified by creating
new operations.
-/
@[local grind]
def LocalRewritePattern.ReturnCtxChanges (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  WfIRContext.WithCreatedOps ctx newCtx

/--
When there is a match and no errors, the returned operations are exactly the new ones
created in the pattern.
-/
def LocalRewritePattern.ReturnOps
  (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues,
  pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ newOp, newOp ∈ newOps ↔ newOp.InBounds newCtx.raw ∧ ¬newOp.InBounds ctx.raw

/--
The pattern returns the same number of values as the number of results of the matched operation.
-/
def LocalRewritePattern.ReturnValues (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op (_ : op.InBounds ctx.raw) newCtx newOps newValues,
  pattern ctx op = some (newCtx, some (newOps, newValues)) →
  newValues.size = op.getNumResults! ctx.raw

/--
Asserts that a state refines pointwise another state at every value dominating
the given insert point.
Also, the memory states are the same.
-/
def InterpreterState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo} (state : InterpreterState ctx)
    (state' : InterpreterState ctx') (insertPoint : InsertPoint) : Prop :=
  state.memory = state'.memory ∧
  ∀ (val : ValuePtr), ValuePtr.dominatesIp val insertPoint ctx →
  ∀ sourceVar, state.variables.getVar? val = some sourceVar →
  ∃ targetVar, state'.variables.getVar? val = some targetVar ∧ sourceVar ⊒ targetVar

/--
Preservation of semantics for a local rewrite pattern.
If the pattern matches an operation and return new operations and values, then interpreting
the matched operation in a state is refined by interpreting the new operations in a refined state.
-/
def LocalRewritePattern.PreservesSemantics
  (pattern : LocalRewritePattern OpCode)
  (_ : ReturnOps pattern) (_ : ReturnCtxChanges pattern) : Prop :=
  ∀ ctx (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified) (op : OperationPtr) (opInBounds : op.InBounds ctx.raw),
  ∀ newCtx newOps newValues (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))),
  ∀ (state : InterpreterState ctx), state.EquationLemmaAt (InsertPoint.before op) →
  ∀ newState cf, interpretOp op state = some (newState, cf) →
  ∀ sourceValues, (op.getResults ctx.raw).mapM (newState.variables.getVar? ·) = some sourceValues →
  ∀ (state' : InterpreterState newCtx), state'.EquationLemmaAt (InsertPoint.before op) →
  state.isRefinedByAt state' (InsertPoint.before op) →
  ∃ newState',
    interpretOpList newOps.toList state' (by grind [ReturnOps]) = some (newState', cf) ∧
    newState.memory = newState'.memory ∧
    ∃ targetValues,
      newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
      sourceValues ⊒ targetValues
