import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.Interpreter.Refinement.Basic
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
All values returned by the pattern are in bounds of the new context.
-/
def LocalRewritePattern.ReturnValuesInBounds (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ v ∈ newValues, v.InBounds newCtx.raw

/--
No value returned by the pattern is one of `op`'s *own* result pointers. This rules out two problems
with the driver's "redirect `op`'s results to `newValues`, then erase `op`" pipeline: (a) a `newValue`
equal to a result of `op` would dangle once `op` is erased; (b) it would make the sequential redirect
fold chain instead of matching the parallel value renaming `σ`.

This replaces the old `ReturnValuesNotSourceResults`, which *also* forbade results of surviving
(pre-existing) operations. That extra restriction is unnecessary: a returned value may now be a result
of an operation already in `ctx`, provided it is in scope at `op` (`ReturnValuesDominate`). This is
what makes general forwarding `x + 0 → x` sound — `x` may be a block argument *or* a result of an
operation defined before `op`. -/
def LocalRewritePattern.ReturnValuesNotOwnResults (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ v ∈ newValues, ∀ m, v ≠ (op.getResult m : ValuePtr)

/--
Every produced value that already exists in the source context (a *forwarded* pre-existing value)
dominates the program point before `op`: it is in scope at `op`'s use site. Produced values that are
fresh (results of the inserted `newOps`, not in bounds of `ctx`) are excluded by the `v.InBounds`
guard — they are inserted before `op` and dominate it by construction.

This is the SSA-validity condition for forwarding. Together with source dominance-wellformedness it is
exactly what discharges the (dominance-scoped) `ReflectsResults o o` frame clause for a surviving
operation `o` whose result is forwarded: `op`'s own result cannot dominate the point before `o` while
`o`'s forwarded result dominates the point before `op` (SSA antisymmetry,
`WfIRContext.Dom.not_opResult_dominatesIp_before_cycle`). It admits any in-scope value — a block
argument or a result of an operation defined before `op` (`x + 0 → x`).
-/
def LocalRewritePattern.ReturnValuesDominate (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx op newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ v ∈ newValues, v.InBounds ctx.raw → v.dominatesIp (InsertPoint.before op) ctx

/--
Indexed access on the returned values is in bounds of the new context.
Discharges the second `sorry` in `LocalRewritePattern.Mapping`.
-/
theorem LocalRewritePattern.ReturnValuesInBounds.getElem!_inBounds
    {pattern : LocalRewritePattern OpCode}
    (hReturn : pattern.ReturnValuesInBounds)
    (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues)))
    {index : Nat} (hindex : index < newValues.size) :
    newValues[index]!.InBounds newCtx.raw := by
  rw [getElem!_pos newValues index hindex]
  exact hReturn ctx op newCtx newOps newValues hpattern newValues[index] (Array.getElem_mem hindex)

/--
A value that is in bounds of the input context is also in bounds of the new context returned
by the pattern. Discharges the third `sorry` in `LocalRewritePattern.Mapping`.
-/
theorem LocalRewritePattern.ReturnCtxChanges.valuePtr_inBounds
    {pattern : LocalRewritePattern OpCode}
    (hReturn : pattern.ReturnCtxChanges)
    (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues)))
    {v : ValuePtr} (vInBounds : v.InBounds ctx.raw) :
    v.InBounds newCtx.raw := by
  have hCreated := hReturn ctx op newCtx newOps newValues hpattern
  have := hCreated.inBounds_mono (GenericPtr.value v) (by grind)
  grind

def LocalRewritePattern.mapping
    {pattern : LocalRewritePattern OpCode}
    (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hreturn : pattern.ReturnValuesInBounds := by grind)
    (hreturn₂ : pattern.ReturnValues := by grind)
    (hreturn₃ : pattern.ReturnCtxChanges := by grind) :
    ValueMapping ctx newCtx :=
  fun ⟨v, vInBounds⟩ =>
    if h : v ∈ op.getResults! ctx.raw then
      let index := (op.getResults! ctx.raw).idxOf v
      have : v = op.getResult index := by grind
      ⟨newValues[index]!, by
        apply LocalRewritePattern.ReturnValuesInBounds.getElem!_inBounds hreturn hpattern
        grind [LocalRewritePattern.ReturnValues]⟩
    else
      ⟨v, by grind⟩

/--
Preservation of semantics for a local rewrite pattern.
If the pattern matches an operation and return new operations and values, then interpreting
the matched operation in a state is refined by interpreting the new operations in a refined state.
-/
def LocalRewritePattern.PreservesSemantics
  (pattern : LocalRewritePattern OpCode)
  (_ : pattern.ReturnOps) (_ : pattern.ReturnCtxChanges)
  (_ : pattern.ReturnValuesInBounds) (_ : pattern.ReturnValues) : Prop :=
  ∀ ctx (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified) (op : OperationPtr) (opInBounds : op.InBounds ctx.raw),
  ∀ newCtx newOps newValues (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))),
  ∀ (state : InterpreterState ctx), state.EquationLemmaAt (InsertPoint.before op) →
  ∀ newState cf, interpretOp op state = some (newState, cf) →
  ∀ sourceValues, (op.getResults ctx.raw).mapM (newState.variables.getVar? ·) = some sourceValues →
  ∀ (state' : InterpreterState newCtx), state'.EquationLemmaAt (InsertPoint.before op) →
  state'.DefinesDominating (InsertPoint.before op) →
  state.isRefinedByAt state' (LocalRewritePattern.mapping hpattern) (.at (.before op)) (.at (.before op)) →
  ∃ newState',
    interpretOpList newOps.toList state' (by grind [ReturnOps]) = some (newState', cf) ∧
    newState.memory = newState'.memory ∧
    ∃ targetValues,
      newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
      sourceValues ⊒ targetValues
