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

/-- `createEmptyOp` leaves a pre-existing operation's properties (at every op code) untouched: it only
`set`s the fresh `newOp`'s record. The shipped `getProperties!_createEmptyOp` is code-specific. -/
theorem OperationPtr.getProperties!_createEmptyOp_ne
    (h : Rewriter.createEmptyOp rawCtx opType properties = some (rawCtx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! rawCtx' oc = operation.getProperties! rawCtx oc := by
  simp only [Rewriter.createEmptyOp, OperationPtr.allocEmpty] at h
  grind [OperationPtr.getProperties!, OperationPtr.set, OperationPtr.get!]

/-- A `WfRewriter.createOp` leaves a pre-existing operation's properties (at every op code) untouched:
only the fresh `newOp` gets properties, and the init steps touch only results/regions/operands. The
code-specific `getProperties!_WfRewriter_createOp` covers only the created op's own type. -/
theorem OperationPtr.getProperties!_WfRewriter_createOp_ne
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      none h₁ h₂ h₃ h₄ = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx'.raw oc = operation.getProperties! ctx.raw oc := by
  simp only [WfRewriter.createOp] at h
  grind [Rewriter.createOp, OperationPtr.getProperties!_createEmptyOp_ne,
    OperationPtr.getProperties!_initOpRegions]

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
