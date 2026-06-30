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
  state.isRefinedByAt state' (LocalRewritePattern.mapping hpattern) (.at (.before op)) (.at (.before op)) →
  ∃ newState',
    interpretOpList newOps.toList state' (by grind [ReturnOps]) = some (newState', cf) ∧
    newState.memory = newState'.memory ∧
    ∃ targetValues,
      newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
      sourceValues ⊒ targetValues

/--
Applying the pattern through the standard driver (`RewritePattern.fromLocalRewrite`) preserves
dominance-wellformedness: rewriting a `Dom` context yields a `Dom` context. This is the structural
counterpart of `PreservesSemantics`'s `ctxDom` hypothesis — where that *assumes* source dominance, this
*propagates* it across the op-list surgery the driver performs (insert `newOps` before `op`, redirect
`op`'s results onto `newValues`, erase `op`). That surgery does not preserve dominance for an arbitrary
pattern, so each concrete pattern must discharge this obligation (typically from `ReturnValuesDominate`
and the SSA structure of its `newOps`). -/
def LocalRewritePattern.RewritePreservesDom (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) (rewriter' : PatternRewriter OpCode),
    RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter' →
    rewriter.ctx.Dom → rewriter'.ctx.Dom

/--
Applying the pattern through the standard driver (`RewritePattern.fromLocalRewrite`) preserves
verification: rewriting a `Verified` context yields a `Verified` context. Like `RewritePreservesDom`,
this propagates a source well-formedness invariant across the driver's op-list surgery, and must be
discharged per concrete pattern. -/
def LocalRewritePattern.RewritePreservesVerified (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) (rewriter' : PatternRewriter OpCode),
    RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter' →
    rewriter.ctx.Verified → rewriter'.ctx.Verified

/--
Applying the pattern through the standard driver (`RewritePattern.fromLocalRewrite`) leaves every
produced value dominating the post-insertion point in the matched operation's block: the end of the
inserted `newOps` span (`afterLast newOps (atStart! block)`) in the rewritten context. This is the
SSA-validity condition on produced values — fresh results of inserted `newOps` are defined within the
span, and forwarded pre-existing values are in scope throughout `block`.

It is the rewritten-context (`rewriter'.ctx`) counterpart of `ReturnValuesDominate`, which states the
source-context (`rewriter.ctx`) version (each forwarded value dominates `before op`). Like
`RewritePreservesDom`/`RewritePreservesVerified`, it is a driver-level fact each concrete pattern must
discharge — typically from `ReturnValuesDominate` together with the SSA structure of its `newOps`. -/
def LocalRewritePattern.RewriteNewValuesDominate (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) (rewriter' : PatternRewriter OpCode),
    RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter' →
    ∀ (block : BlockPtr) (newCtx : WfIRContext OpCode)
      (newOps : Array OperationPtr) (newValues : Array ValuePtr),
    (op.get! rewriter.ctx.raw).parent = some block →
    pattern rewriter.ctx op = some (newCtx, some (newOps, newValues)) →
    ∀ v ∈ newValues,
      v.dominatesIp (InsertPoint.afterLast newOps.toList rewriter'.ctx.raw
        (InsertPoint.atStart! block rewriter'.ctx.raw)) rewriter'.ctx

/--
Applying the pattern through the standard driver (`RewritePattern.fromLocalRewrite`) preserves
block-level dominance: any two in-bounds blocks dominate each other in the rewritten context exactly
when they do in the source context. The driver edits only the operation list of the matched
operation's block (insert `newOps` before `op`, redirect `op`'s results, erase `op`); it never adds
or removes a block, nor alters region structure. That op-list surgery does not preserve the block
CFG for an *arbitrary* pattern — replacing a block's terminator can re-route its successors — so, like
`RewritePreservesDom`/`RewritePreservesVerified`, each concrete pattern must discharge this obligation
(typically because its `newOps` reproduce the matched operation's control-flow behaviour, leaving every
block's successor edges intact). -/
def LocalRewritePattern.RewritePreservesBlockDominance (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) (rewriter' : PatternRewriter OpCode),
    RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter' →
    ∀ (b₁ b₂ : BlockPtr), b₁.InBounds rewriter.ctx.raw → b₂.InBounds rewriter.ctx.raw →
      (b₁.dominates b₂ rewriter'.ctx ↔ b₁.dominates b₂ rewriter.ctx)

/--
The bundle of correctness obligations a `LocalRewritePattern` must satisfy for the soundness
results (notably `RewrittenAt.of_fromLocalRewrite` and the soundness lift built on it) to apply.
Bundling them into a single structure avoids threading every obligation as a separate argument.
Later fields may refer to earlier ones, so `preservesSemantics` reuses the `Return*` fields it
depends on.
-/
structure LocalRewritePattern.Valid (pattern : LocalRewritePattern OpCode) : Prop where
  /-- The pattern returns the input context whenever there are no errors and no match. -/
  returnsCtxNoChanges : pattern.ReturnsCtxNoChanges
  /-- On a match, the output context is only modified by creating new operations. -/
  returnCtxChanges : pattern.ReturnCtxChanges
  /-- On a match, the returned operations are exactly the newly created ones. -/
  returnOps : pattern.ReturnOps
  /-- The pattern returns one value per result of the matched operation. -/
  returnValues : pattern.ReturnValues
  /-- All returned values are in bounds of the new context. -/
  returnValuesInBounds : pattern.ReturnValuesInBounds
  /-- No returned value is one of `op`'s own result pointers. -/
  returnValuesNotOwnResults : pattern.ReturnValuesNotOwnResults
  /-- Every forwarded pre-existing returned value dominates the point before `op`. -/
  returnValuesDominate : pattern.ReturnValuesDominate
  /-- Interpreting the matched operation is refined by interpreting the new operations. -/
  preservesSemantics :
    pattern.PreservesSemantics returnOps returnCtxChanges returnValuesInBounds returnValues
  /-- The driver-applied rewrite preserves dominance-wellformedness. -/
  rewritePreservesDom : pattern.RewritePreservesDom
  /-- The driver-applied rewrite preserves verification. -/
  rewritePreservesVerified : pattern.RewritePreservesVerified
  /-- Every produced value dominates the post-insertion point in the matched operation's block. -/
  rewriteNewValuesDominate : pattern.RewriteNewValuesDominate
  /-- The driver-applied rewrite preserves block-level dominance. -/
  rewritePreservesBlockDominance : pattern.RewritePreservesBlockDominance
