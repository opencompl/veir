import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBinaryW

namespace Veir

/-!
## Correctness of `uaddSat_local`

`llvm.intr.uadd.sat` on a 64-bit integer is lowered to LLVM's RV64+Zbb `umin` idiom
`uadd.sat(a, b) -> umin(a, ~b) + b`:
`unrealized_conversion_cast` (each operand to a register) → `riscv.xori -1` (bitwise-not of the
second register, `~b`) → `riscv.minu` (of the first register and `~b`) → `riscv.add` (that min plus
the second register) → `unrealized_conversion_cast` (back to the integer type).

`uaddSat` fits neither `lowerBinaryRegLocal` (it emits *three* register ops, not one) nor `abs_local`
(it has *two* operands, not one). It is therefore proven bespoke, in the same shape as the sibling
`usubSat_local` proof: the two-operand `castToRegLocal`/`castToRegLocal` prefix followed by a
straight-line register chain, except here the chain has an extra immediate step (`xori -1`, the
immediate analogue of the plain unary-register forward lemma) and the second cast register (`rReg`)
must be kept alive across the `xori`/`minu` steps to reach the final `add`. It is `i64`-only, so
there is no bitwidth branch.
-/

/-- Forward-interpretation lemma for the immediate `riscv.xori`. Like
    `interpretOp_riscv_srli_forward`, the emitted register is a function of the op's *immediate*,
    read from its properties (as a `BitVec 12`), so the caller supplies that immediate as `k`
    together with the reduction `hImm` of the op's stored property value. Interpreting the op
    succeeds, leaves memory untouched, binds the result to `.reg (Data.RISCV.xori k r)`, and leaves
    every non-result value unchanged. -/
theorem interpretOp_riscv_xori_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 12}
    (hType : theOp.getOpType! ctx.raw = .riscv .xori)
    (hImm : BitVec.ofInt 12 (theOp.getProperties! ctx.raw (.riscv .xori)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.xori k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.xori k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Correctness of the `add (minu (xori -1 ·) ·) ·` lowering of a 64-bit `llvm.intr.uadd.sat`: the
    round trip `int × int → reg × reg → xori/minu/add → int` refines `uaddSat`. (`xt`/`yt` are the
    possibly-more-defined target-side values of the operands.) The interpreter applies each binary
    data-level op as `RISCV.op op2 op1`, so the target expression takes `(toReg yt)` first in `add`
    and `(xori -1 (toReg yt))` first in `minu`. -/
theorem uaddSat_isRefinedBy_toInt_add_minu {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.uaddSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.add (LLVM.Int.toReg yt)
          (Data.RISCV.minu (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg yt))
            (LLVM.Int.toReg xt))) 64 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Correctness of the `uaddSat_local` lowering: the `castToReg → castToReg → xori -1 → minu → add →
    castBack` round trip refines `llvm.intr.uadd.sat`. -/
theorem uaddSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics uaddSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, uaddSat_local, createRISCVUnitLocal,
    createRISCVImmLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchUaddSat op ctx.raw).isSome := by
    cases hM : matchUaddSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchUaddSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__uadd__sat opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Both operand types and the result type are the integer type `intType`.
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand values and their `uaddSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.uaddSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__uadd__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__uadd__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.uaddSat x y)], mem, none)) := by
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
        rw [hEq] at h; injection h with h; injection h with h; exact h.symm)
      hinterp hLhsType hRhsType
  subst hCf
  -- The matched operands dominate the rewrite point in the source context.
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition' [hBw] hpattern
  -- Source value: `op`'s single result is `uaddSat` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `lhs`/`rhs` are not among `op`'s results.
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two `castToRegLocal` creations, transporting both operand dominance facts through.
  peelCastToRegLocal₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelCastToRegLocal₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  -- Freshness facts, used to keep earlier values alive across later interpretation steps.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsNeLCastRes : ∀ i, rhs ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hRhsIn
    rw [ValuePtr.inBounds_opResult] at hRhsIn
    obtain ⟨hIn, -⟩ := hRhsIn
    exact hLCastFresh hIn
  -- Peel the `xori`, the `minu`, the `add`, and the `replaceWithRegLocal` creations.
  peelOpCreation!₂ hpattern ctx₃ xoriOp hXori hDomL₂ hDomL₃ hDomR₂ hDomR₃
  peelOpCreation!₂ hpattern ctx₄ minuOp hMinu hDomL₃ hDomL₄ hDomR₃ hDomR₄
  peelOpCreation!₂ hpattern ctx₅ addOp hAdd hDomL₄ hDomL₅ hDomR₄ hDomR₅
  -- `op` and `addOp`'s result stay in bounds across the five createOps; grind's e-matching cannot
  -- chain this far on its own, so establish the facts the final peel's dischargers need up front.
  have hOpIn₁ : op.InBounds ctx₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hLCast opInBounds
  have hOpIn₂ : op.InBounds ctx₂.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hRCast hOpIn₁
  have hOpIn₃ : op.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hXori hOpIn₂
  have hOpIn₄ : op.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hMinu hOpIn₃
  have hOpInBounds₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hAdd hOpIn₄
  have hAddIn₅ : addOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds addOp hAdd
  have hAddNRes₅ : addOp.getNumResults! ctx₅.raw = 1 := by
    grind [OperationPtr.getNumResults!_WfRewriter_createOp hAdd (operation := addOp)]
  have hAddResIn₅ : (ValuePtr.opResult (addOp.getResult 0)).InBounds ctx₅.raw := by
    rw [ValuePtr.inBounds_opResult]
    exact OperationPtr.getResult_inBounds addOp hAddIn₅ 0
      (by rw [← OperationPtr.getNumResults!_eq_getNumResults hAddIn₅, hAddNRes₅]; decide)
  peelReplaceWithRegLocal₂ hpattern ctx₆ castBackOp hCastBack hDomL₅ hDomL₆ hDomR₅ hDomR₆
  cleanupHpattern hpattern
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtxL hDomL₆ lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
      hDomCtxR hDomR₆ rNotOp
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- Structural facts about the six created ops (opcode transports seeded explicitly).
  have hLCastType : lcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXori (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMinu (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastType : rcastOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hXori (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMinu (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hXoriType : xoriOp.getOpType! ctx₆.raw = .riscv .xori := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hXori (operation := xoriOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMinu (operation := xoriOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := xoriOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := xoriOp)]
  have hMinuType : minuOp.getOpType! ctx₆.raw = .riscv .minu := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hMinu (operation := minuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := minuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := minuOp)]
  have hAddType : addOp.getOpType! ctx₆.raw = .riscv .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := addOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := addOp)]
  have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hLCastOperands : lcastOp.getOperands! ctx₆.raw = #[lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXori (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMinu (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastOperands : rcastOp.getOperands! ctx₆.raw = #[rhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hXori (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMinu (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hXoriOperands : xoriOp.getOperands! ctx₆.raw
      = #[ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hXori (operation := xoriOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMinu (operation := xoriOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := xoriOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xoriOp)]
  have hMinuOperands : minuOp.getOperands! ctx₆.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (xoriOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMinu (operation := minuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := minuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := minuOp)]
  have hAddOperands : addOp.getOperands! ctx₆.raw
      = #[ValuePtr.opResult (minuOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := addOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := addOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (addOp.getResult 0)] := by grind
  -- The `xori` immediate is `-1`.
  have hXoriProps : xoriOp.getProperties! ctx₆.raw (.riscv .xori) = mkRISCVImm (-1) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAdd (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hMinu (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp hXori (operation := xoriOp)]
    rw [if_pos rfl]; rfl
  have hXoriImm : BitVec.ofInt 12 (xoriOp.getProperties! ctx₆.raw (.riscv .xori)).value.value
      = BitVec.ofInt 12 (-1) := by rw [hXoriProps]; simp [mkRISCVImm]
  -- The cast-back op's result type is the integer type `i64`.
  have hCBType : ((op.getResult 0).get! ctx₅.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₅.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hAdd
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hMinu
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hXori
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hRCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hLCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hLCastResTypes : lcastOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXori (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMinu (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastResTypes : rcastOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXori (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMinu (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hXoriResTypes : xoriOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXori (operation := xoriOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMinu (operation := xoriOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := xoriOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xoriOp)]
  have hMinuResTypes : minuOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hMinu (operation := minuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := minuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := minuOp)]
  have hAddResTypes : addOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := addOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := addOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  -- Interpretation tail: execute `interpretOpList [lcast, rcast, xori, minu, add, castBack]` in
  -- `state'`. The frame clauses carry earlier bindings across later steps.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hLCastType hLCastOperands hLCastResTypes hLVal'
  have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₆.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw rhs lcastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hRhsNeLCastRes i)
  have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
    rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hRCastType hRCastOperands hRCastResTypes hRVal₁
  -- Carry the `lcast` register through the `rcast` and `xori` steps (needed by `minu`).
  have hLCastNotRCastRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₆.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
  -- The `xori` step: `~(toReg yt)`.
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_xori_forward (state := s₂) (inBounds := by grind)
      (k := BitVec.ofInt 12 (-1)) hXoriType hXoriImm hXoriOperands hXoriResTypes hRes₂
  have hLCastNotXoriRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ xoriOp.getResults! ctx₆.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) xoriOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLRes₃ : s₃.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₃ _ hLCastNotXoriRes]; exact hLRes₂
  have hRCastNotXoriRes :
      ValuePtr.opResult (rcastOp.getResult 0) ∉ xoriOp.getResults! ctx₆.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
        (ValuePtr.opResult (rcastOp.getResult 0)) xoriOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ hRCastNotXoriRes]; exact hRes₂
  -- The `minu` step: `minu (~(toReg yt)) (toReg xt)`.
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.minu r₂ r₁) (fun _ _ _ _ => rfl) hMinuType hMinuOperands
      hMinuResTypes hLRes₃ hRes₃
  -- Carry the `rcast` register through the `minu` step (needed by `add`).
  have hRCastNotMinuRes :
      ValuePtr.opResult (rcastOp.getResult 0) ∉ minuOp.getResults! ctx₆.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₆.raw
        (ValuePtr.opResult (rcastOp.getResult 0)) minuOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hRRes₄ : s₄.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₄ _ hRCastNotMinuRes]; exact hRRes₃
  -- The `add` step: `add (toReg yt) (minu …)`.
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.add r₂ r₁) (fun _ _ _ _ => rfl) hAddType hAddOperands
      hAddResTypes hRes₄ hRRes₄
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_castBack_forward (state := s₅) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₅
  refine ⟨s₆, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, liftM, monadLift,
      MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.add (LLVM.Int.toReg yt)
          (Data.RISCV.minu (Data.RISCV.xori (BitVec.ofInt 12 (-1)) (LLVM.Int.toReg yt))
            (LLVM.Int.toReg xt))) 64)], ?_, ?_⟩
    · simp [hRes₆, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using uaddSat_isRefinedBy_toInt_add_minu hxtRef hytRef⟩

end Veir
