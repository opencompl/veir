import Veir.IR.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Dominance
import Veir.Passes.Matching
import Veir.Verifier
import Veir.Passes.InstructionSelection.Common
import Veir.Interpreter

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {rawCtx rawCtx' : IRContext OpInfo} {ctx ctx' : WfIRContext OpInfo}

/-!
  This file contains lemmas that are useful when proving that a local rewrite preserves
  semantics with `PreservesSemantics`.
-/

/--
Read a refined integer operand in a `PreservesSemantics` proof: a value `v` that is not one of the
matched op's results maps to itself through `LocalRewritePattern.mapping`, so given its integer
value in the source state, the value-refinement hypothesis and `DefinesDominating` for the target
state yield its integer value in the target state, refined by the source one.
-/
theorem LocalRewritePattern.exists_refined_int_getVar?
    {ctx : WfIRContext OpCode}
    {ipIn : ip.InBounds ctx.raw}
    {pattern : LocalRewritePattern OpCode}
    {hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃) (.at ip) (.at ip) ipIn ipIn')
    (state'Dom : state'.DefinesDominating ip ipIn')
    (vIn : v.InBounds ctx.raw)
    (hxVal : state.variables.getVar? v = some (RuntimeValue.int bw x))
    (hDomCtx : v.dominatesIp ip ctx) (hDom' : v.dominatesIp ip newCtx)
    (hNotRes : v ∉ op.getResults! ctx.raw) :
    ∃ xt, state'.variables.getVar? v = some (RuntimeValue.int bw xt) ∧ x ⊒ xt := by
  have ⟨tv, hTv⟩ := InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (hreturn₃.valuePtr_inBounds hpattern vIn) hDom'
  have hRef : RuntimeValue.int bw x ⊒ tv := by
    grind [LocalRewritePattern.mapping, valueRefinement v]
  grind [RuntimeValue.int_of_isRefinedBy hRef]

/-- Byte analogue of `exists_refined_int_getVar?`: read the target-side value of a `byte`-typed
operand that refines the source-side one. -/
theorem LocalRewritePattern.exists_refined_byte_getVar?
    {ctx : WfIRContext OpCode}
    {ipIn : ip.InBounds ctx.raw}
    {pattern : LocalRewritePattern OpCode}
    {hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃) (.at ip) (.at ip) ipIn ipIn')
    (state'Dom : state'.DefinesDominating ip ipIn')
    (vIn : v.InBounds ctx.raw)
    (hxVal : state.variables.getVar? v = some (RuntimeValue.byte bw x))
    (hDomCtx : v.dominatesIp ip ctx) (hDom' : v.dominatesIp ip newCtx)
    (hNotRes : v ∉ op.getResults! ctx.raw) :
    ∃ xt, state'.variables.getVar? v = some (RuntimeValue.byte bw xt) ∧ x ⊒ xt := by
  have ⟨tv, hTv⟩ := InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (hreturn₃.valuePtr_inBounds hpattern vIn) hDom'
  have hRef : RuntimeValue.byte bw x ⊒ tv := by
    grind [LocalRewritePattern.mapping, valueRefinement v]
  grind [RuntimeValue.byte_of_isRefinedBy hRef]

/-- A value that exists in a context `ctx` is never a result of an operation that is *not* in
bounds of `ctx` (e.g. a freshly created op), in any context `ctx'`: result membership pins the
value's operation pointer, and an in-bounds `opResult` value forces its operation in bounds.
Used to discharge the frame-clause side conditions when symbolically executing a chain of
created ops. -/
theorem ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
    {value : ValuePtr} {op : OperationPtr} {ctx ctx' : IRContext OpInfo}
    (hval : value.InBounds ctx) (hop : ¬ op.InBounds ctx) :
    value ∉ op.getResults! ctx' := by
  intro hmem
  obtain ⟨i, -, rfl⟩ := (OperationPtr.getResults!.mem_iff_exists_index).mp hmem
  exact hop (by grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult])

/-- Reducing `WfRewriter.createOp!` at a `none` insertion point (the local-rewrite case): when all
    the operand/block-operand/region in-bounds side conditions hold, it is just `createOp`. -/
theorem WfRewriter.createOp!_none_eq {wfCtx : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds wfCtx.raw)
    (hblock : ∀ oper, oper ∈ blockOperands → oper.InBounds wfCtx.raw)
    (hreg : ∀ reg, reg ∈ regions → reg.InBounds wfCtx.raw) :
    WfRewriter.createOp! wfCtx opType resultTypes operands blockOperands regions properties none
      = WfRewriter.createOp wfCtx opType resultTypes operands blockOperands regions properties none
          hoper hblock hreg := by
  simp only [WfRewriter.createOp!, dif_pos hoper, dif_pos hblock, dif_pos hreg]

/-- Invert a successful `WfRewriter.createOp!` at a `none` insertion point: since every failing
    side condition makes `createOp!` panic (i.e. return `none`), a `some` result recovers the
    in-bounds side conditions together with the plain `createOp` equation.

    Prefer this over `createOp!_none_eq` when peeling a creation chain: it binds the side-condition
    proofs to local hypotheses rather than inlining them into the type of the creation hypothesis.
    Inlined proofs are copied into the *implicit* arguments of every downstream lemma applied to
    that hypothesis (`createOp_inBounds_mono`, `dominatesIp_before_WfRewriter_createOp`, …), and
    those copies are in turn inlined into the next creation hypothesis, so a chain of `n` creations
    builds a proof term of size exponential in `n`. -/
theorem WfRewriter.createOp!_none_some {wfCtx : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    {ctx' : WfIRContext OpInfo} {newOp : OperationPtr}
    (h : WfRewriter.createOp! wfCtx opType resultTypes operands blockOperands regions properties none
      = some (ctx', newOp)) :
    ∃ (hoper : ∀ oper, oper ∈ operands → oper.InBounds wfCtx.raw)
      (hblock : ∀ oper, oper ∈ blockOperands → oper.InBounds wfCtx.raw)
      (hreg : ∀ reg, reg ∈ regions → reg.InBounds wfCtx.raw),
      WfRewriter.createOp wfCtx opType resultTypes operands blockOperands regions properties none
        hoper hblock hreg = some (ctx', newOp) := by
  unfold WfRewriter.createOp! at h
  split at h
  · split at h
    · split at h
      · exact ⟨_, _, _, h⟩
      · simp [panicWithPosWithDecl, panic, panicCore] at h
    · simp [panicWithPosWithDecl, panic, panicCore] at h
  · simp [panicWithPosWithDecl, panic, panicCore] at h

/-- Creating an operation at a `none` insertion point preserves dominance of a value at the program
    point before any *other* operation `op'`: a freshly created (detached) operation `newOp ≠ op'`
    cannot change whether `value` dominates `before op'`.

    Axiomatised because `Veir.ValuePtr.dominatesIp` is opaque and the rewriter API currently exposes
    no dominance-preservation lemma; this is the dominance analogue of the in-bounds preservation
    lemmas for `WfRewriter.createOp`. -/
axiom ValuePtr.dominatesIp_before_WfRewriter_createOp
    {wfCtx wfCtx' : WfIRContext OpInfo} {opType : OpInfo}
    {resultTypes operands blockOperands regions} {properties : HasOpInfo.propertiesOf opType}
    {hoper hblock hreg hins} {newOp op' : OperationPtr} {value : ValuePtr}
    (h : WfRewriter.createOp wfCtx opType resultTypes operands blockOperands regions properties none
          hoper hblock hreg hins = some (wfCtx', newOp))
    (hop' : op'.InBounds wfCtx.raw) (hne : op' ≠ newOp) :
    value.dominatesIp (InsertPoint.before op') wfCtx'
      ↔ value.dominatesIp (InsertPoint.before op') wfCtx
