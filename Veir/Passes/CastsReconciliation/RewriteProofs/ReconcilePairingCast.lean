import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.Casting
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.CastsReconciliation.RewriteProofs.CommonCast
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas

namespace Veir

/-! ## Correctness of `reconcilePairingCastLocal`

`reconcilePairingCastLocal legal` erases a cast whose operand is itself a cast back from the
original type (`X → Y → X`, legal per `legal X Y`). It is correct exactly when that round trip is
the identity on runtime values, which is the single hypothesis `hRoundTrip` of the shared theorem
below. Two of the four `legal` predicates satisfy it:

* `isRegToI64RoundTrip` — `Int.toReg (Reg.toInt r 64) = r`;
* `isRiscvRegToPtrCast` — pointer/register values carry no poison and the round trip is the
  identity in both directions.

The other two, `isI64ToRegRoundTrip` and `isRiscvRegToI32Cast`, are **not** provable and have no
theorem here. Both start from an integer: `Int.toReg` maps `poison` to the concrete `0#64`, so the
round trip *freezes* poison. In a state where the source value is `poison`, the source program
(with the casts) produces `0` while the rewritten program produces `poison`, and `0 ⊒ poison` is
false — the refinement `sourceValues ⊒ targetValues` fails. This is the same obstruction as the
`freeze` lowering under the deterministic-zero poison model. Unblocking either rewrite needs a
different cast semantics: an `Int.toReg` that raises UB on poison, or a nondeterministic freeze
model in which the rewritten program's `poison` may take the value `0`. -/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for every `reconcilePairingCastLocal legal` instance: given that the
`legal` round trip is the identity on conforming runtime values, erasing it preserves semantics. -/
theorem reconcilePairingCastLocal_preservesSemantics {legal : TypeAttr → TypeAttr → Bool}
    (hRoundTrip : ∀ (tin tinter : TypeAttr) (v w u : RuntimeValue), legal tin tinter = true →
      v.Conforms tin → castRuntimeValue tinter v = some w → castRuntimeValue tin w = some u →
      u = v)
    {h : LocalRewritePattern.ReturnOps (reconcilePairingCastLocal legal)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (reconcilePairingCastLocal legal)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (reconcilePairingCastLocal legal)}
    {h₄ : LocalRewritePattern.ReturnValues (reconcilePairingCastLocal legal)} :
    LocalRewritePattern.PreservesSemantics (reconcilePairingCastLocal legal) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, reconcilePairingCastLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer matcher.
  have hMatchSome : (matchCastOp op ctx.raw).isSome := by
    cases hM : matchCastOp op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨input, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the `.opResult` destructuring: the operand must be defined by an operation.
  obtain ⟨castPtr, rfl⟩ : ∃ castPtr, input = ValuePtr.opResult castPtr := by
    cases input with
    | opResult castPtr => exact ⟨castPtr, rfl⟩
    | blockArgument _ => simp at hpattern
  simp only [] at hpattern
  -- Peel the inner matcher.
  have hMatchSome' : (matchCastOp castPtr.op ctx.raw).isSome := by
    cases hM : matchCastOp castPtr.op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨parentInput, hMatch'⟩ := Option.isSome_iff_exists.mp hMatchSome'
  rw [hMatch'] at hpattern
  simp only [] at hpattern
  -- Peel the two guards: the result type is the parent's input type, and the pair is legal.
  have hTyEq : ((op.getResult 0).get! ctx.raw).type = parentInput.getType! ctx.raw := by
    rcases Decidable.em (((op.getResult 0).get! ctx.raw).type = parentInput.getType! ctx.raw)
      with hty | hty
    · exact hty
    · rw [if_neg hty] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hTyEq] at hpattern
  have hLegal : legal (parentInput.getType! ctx.raw)
      ((ValuePtr.opResult castPtr).getType! ctx.raw) = true := by
    rcases Decidable.em (legal (parentInput.getType! ctx.raw)
        ((ValuePtr.opResult castPtr).getType! ctx.raw) = true) with hl | hl
    · exact hl
    · rw [if_pos (by simpa using hl)] at hpattern
      exact absurd hpattern (by simp)
  rw [if_neg (by rw [hLegal]; simp)] at hpattern
  -- Read off the pattern's outputs.
  obtain ⟨rfl, rfl, rfl⟩ : ctx = newCtx ∧ newOps = #[] ∧ newValues = #[parentInput] := by
    simp at hpattern; grind
  -- Syntactic facts from the outer match.
  obtain ⟨hOpType, hNRes, hOperands⟩ := matchCastOp_implies hMatch
  have hOperandMem : ValuePtr.opResult castPtr ∈ op.getOperands! ctx.raw := by
    rw [hOperands]; simp
  -- `op` has a single result; pin the source-value array's shape now, while the context is small
  -- enough for `grind` (the round-trip hypothesis makes it wander later).
  have hResults : op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] := by
    clear hRoundTrip hpattern; grind
  -- Source side, outer cast: its result is `castRuntimeValue` (at the result type) of `input`.
  obtain ⟨w, u, hInputVal, hCastOuter, hMemEq, hResVal, rfl⟩ :=
    castOp_interpretOp_unfold opInBounds hOpType hNRes hOperands rfl hinterp
  -- Source side, inner cast: `input` holds `castRuntimeValue` (at its type) of `parentInput`.
  obtain ⟨v, w', hParentVal, hCastInner, hInputVal', hParentDom, hParentIn, hParentNotRes⟩ :=
    castOp_getVar?_of_EquationLemmaAt ctxDom opInBounds stateWf hMatch' hOperandMem
  have hww : w' = w := by rw [hInputVal'] at hInputVal; simpa using hInputVal
  rw [hww] at hCastInner
  -- The round trip is the identity, so the outer cast's result is `parentInput`'s value.
  have hConf : v.Conforms (parentInput.getType! ctx.raw) := VariableState.getVar?_conforms hParentVal
  obtain rfl : u = v :=
    hRoundTrip _ _ v w u hLegal hConf hCastInner (by rwa [hTyEq] at hCastOuter)
  -- Source values: `op`'s single result holds `v`.
  rw [hResults] at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Target side: no operation is interpreted, so the target state is `state'`.
  refine ⟨state', by simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, pure, Interp],
    by grind, ?_⟩
  obtain ⟨tv, hTvVal, hTvRef⟩ :=
    LocalRewritePattern.exists_refined_getVar? valueRefinement state'Dom hParentIn hParentVal
      hParentDom hParentDom hParentNotRes
  exact ⟨#[tv], by simp [hTvVal], RuntimeValue.arrayIsRefinedBy_singleton.mpr hTvRef⟩

/-! ### The three provable instantiations -/

/-- What `isRegToI64RoundTrip` says about the two types. -/
theorem isRegToI64RoundTrip_implies {tin tinter : TypeAttr}
    (h : isRegToI64RoundTrip tin tinter = true) :
    (∃ rt, tin.val = .registerType rt) ∧ ∃ it, tinter.val = .integerType it ∧ it.bitwidth = 64 := by
  unfold isRegToI64RoundTrip at h
  split at h <;> simp_all

/-- `reg -> i64 -> reg` is the identity: `Reg.toInt r 64` is the never-poison value of `r`, which
`Int.toReg` maps back to `r`. -/
theorem isRegToI64RoundTrip_roundTrip (tin tinter : TypeAttr) (v w u : RuntimeValue)
    (hLegal : isRegToI64RoundTrip tin tinter = true) (hConf : v.Conforms tin)
    (hInner : castRuntimeValue tinter v = some w) (hOuter : castRuntimeValue tin w = some u) :
    u = v := by
  obtain ⟨⟨rt, htin⟩, it, htinter, hbw⟩ := isRegToI64RoundTrip_implies hLegal
  obtain ⟨a, ha⟩ := tin; obtain ⟨b, hb⟩ := tinter
  simp only at htin htinter; subst htin; subst htinter
  obtain ⟨r, rfl⟩ := RuntimeValue.Conforms.registerType hConf
  simp only [castRuntimeValue, Option.some.injEq] at hInner
  subst hInner
  simp only [castRuntimeValue, Option.some.injEq] at hOuter
  subst hOuter
  rw [hbw, toReg_toInt_64]

theorem reconcilePairingCastLocal_isRegToI64RoundTrip_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (reconcilePairingCastLocal isRegToI64RoundTrip) h h₂ h₃ h₄ :=
  reconcilePairingCastLocal_preservesSemantics isRegToI64RoundTrip_roundTrip

/-- What `isRiscvRegToPtrCast` says about the two types: one of them is a pointer and the other a
register, in either order. -/
theorem isRiscvRegToPtrCast_implies {tin tinter : TypeAttr}
    (h : isRiscvRegToPtrCast tin tinter = true) :
    (∃ pt rt, tin.val = .llvmPointerType pt ∧ tinter.val = .registerType rt) ∨
    (∃ rt pt, tin.val = .registerType rt ∧ tinter.val = .llvmPointerType pt) := by
  unfold isRiscvRegToPtrCast at h
  split at h <;> simp_all

/-- `ptr -> reg -> ptr` and `reg -> ptr -> reg` are both the identity: address and register values
carry no poison, and the two conversions are inverse bit-preserving reinterpretations. -/
theorem isRiscvRegToPtrCast_roundTrip (tin tinter : TypeAttr) (v w u : RuntimeValue)
    (hLegal : isRiscvRegToPtrCast tin tinter = true) (hConf : v.Conforms tin)
    (hInner : castRuntimeValue tinter v = some w) (hOuter : castRuntimeValue tin w = some u) :
    u = v := by
  obtain ⟨a, ha⟩ := tin; obtain ⟨b, hb⟩ := tinter
  rcases isRiscvRegToPtrCast_implies hLegal with ⟨pt, rt, htin, htinter⟩ | ⟨rt, pt, htin, htinter⟩
  · -- `ptr -> reg -> ptr`
    simp only at htin htinter; subst htin; subst htinter
    obtain ⟨addr, rfl⟩ := RuntimeValue.Conforms.llvmPointerType hConf
    simp only [castRuntimeValue, Option.some.injEq] at hInner
    subst hInner
    simp only [castRuntimeValue, Option.some.injEq] at hOuter
    subst hOuter
    simp
  · -- `reg -> ptr -> reg`
    simp only at htin htinter; subst htin; subst htinter
    obtain ⟨r, rfl⟩ := RuntimeValue.Conforms.registerType hConf
    simp only [castRuntimeValue, Option.some.injEq] at hInner
    subst hInner
    simp only [castRuntimeValue, Option.some.injEq] at hOuter
    subst hOuter
    simp

theorem reconcilePairingCastLocal_isRiscvRegToPtrCast_preservesSemantics :
    LocalRewritePattern.PreservesSemantics
      (reconcilePairingCastLocal isRiscvRegToPtrCast) h h₂ h₃ h₄ :=
  reconcilePairingCastLocal_preservesSemantics isRiscvRegToPtrCast_roundTrip

/-- info: 'Veir.reconcilePairingCastLocal_isRegToI64RoundTrip_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 MemoryState.llvmLoad._native.bv_decide.ax_8] -/
#guard_msgs in
#print axioms reconcilePairingCastLocal_isRegToI64RoundTrip_preservesSemantics

/-- info: 'Veir.reconcilePairingCastLocal_isRiscvRegToPtrCast_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 MemoryState.llvmLoad._native.bv_decide.ax_8] -/
#guard_msgs in
#print axioms reconcilePairingCastLocal_isRiscvRegToPtrCast_preservesSemantics

end Veir
