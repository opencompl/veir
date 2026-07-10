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
## Correctness of `usubSat_local`

`llvm.intr.usub.sat` on a 64-bit integer is lowered to LLVM's RV64+Zbb `umax`/`sub` idiom
`usub.sat(a, b) -> umax(a, b) - b`:
`unrealized_conversion_cast` (each operand to a register) → `riscv.maxu` (of the two registers) →
`riscv.sub` (the max minus the second register) → `unrealized_conversion_cast` (back to the integer
type).

`usubSat` fits neither `lowerBinaryRegLocal` (it emits *two* register ops, not one) nor `abs_local`
(it has *two* operands, not one). It is therefore proven bespoke: structurally it is the two-operand
`lowerBinaryRegLocal` `castToRegLocal`/`castToRegLocal` prefix followed by the `abs_local`-style
two-riscv-op chain, except the second op (`sub`) consumes the `maxu` result together with the second
cast register (`rReg`), which must be kept alive across the `maxu` step via its frame clause. It is
`i64`-only, so there is no bitwidth branch.
-/

/-- Correctness of the `sub (maxu ·) ·` lowering of a 64-bit `llvm.intr.usub.sat`: the round trip
    `int × int → reg × reg → maxu/sub → int` refines `usubSat`. (`xt`/`yt` are the possibly-more-
    defined target-side values of the operands.) The interpreter applies each data-level op as
    `RISCV.op op2 op1`, so the target expression takes `(toReg yt)` first in each op. -/
theorem usubSat_isRefinedBy_toInt_sub_maxu {x y xt yt : Data.LLVM.Int 64}
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.usubSat x y ⊒
      RISCV.Reg.toInt
        (Data.RISCV.sub (LLVM.Int.toReg yt)
          (Data.RISCV.maxu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h₁ h₂ ⊢
  obtain ⟨hp₁, hv₁⟩ := h₁
  obtain ⟨hp₂, hv₂⟩ := h₂
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_usubSat] at hnp; grind
  have hynp : y.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_usubSat] at hnp; grind
  have hvd₁ : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  have hvd₂ : y.getValueD = yt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.sub, Data.RISCV.maxu]
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Correctness of the `usubSat_local` lowering: the `castToReg → castToReg → maxu → sub → castBack`
    round trip refines `llvm.intr.usub.sat`. -/
theorem usubSat_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics usubSat_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, usubSat_local, createRISCVUnitLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchUsubSat op ctx.raw).isSome := by
    cases hM : matchUsubSat op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchUsubSat_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_intr__usub__sat opVerif hOpType
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
  -- Unfold the interpretation of the matched op: exposes the operand values and their `usubSat`.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold
      (srcFn := fun {_} x y _ => Data.LLVM.Int.usubSat x y)
      (props := op.getProperties! ctx.raw (.llvm .intr__usub__sat))
      opInBounds hOpType hNumResults hOperands rfl
      (fun bw x y props rt bo mem res h => by
        have hEq : Llvm.interpretOp' .intr__usub__sat props rt #[.int bw x, .int bw y] bo mem
            = some (.ok (#[.int bw (Data.LLVM.Int.usubSat x y)], mem, none)) := by
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
  -- Source value: `op`'s single result is `usubSat` of its operands.
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
  -- Established here (before the later peels and `cleanupHpattern`) so `clear hpattern` succeeds.
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsNeLCastRes : ∀ i, rhs ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hRhsIn
    rw [ValuePtr.inBounds_opResult] at hRhsIn
    obtain ⟨hIn, -⟩ := hRhsIn
    exact hLCastFresh hIn
  -- Peel the `maxu`, the `sub`, and the `replaceWithRegLocal` creations.
  peelOpCreation!₂ hpattern ctx₃ maxuOp hMaxu hDomL₂ hDomL₃ hDomR₂ hDomR₃
  peelOpCreation!₂ hpattern ctx₄ subOp hSub hDomL₃ hDomL₄ hDomR₃ hDomR₄
  peelReplaceWithRegLocal₂ hpattern ctx₅ castBackOp hCastBack hDomL₄ hDomL₅ hDomR₄ hDomR₅
  cleanupHpattern hpattern
  -- Read the refined values `xt`/`yt` of `lhs`/`rhs` in the target state `state'`.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtxL hDomL₅ lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
      hDomCtxR hDomR₅ rNotOp
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  -- Structural facts about the five created ops. The opcode transports are seeded explicitly
  -- because plain `grind` no longer chains them for ops created several contexts back.
  have hLCastType : lcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMaxu (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := lcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastType : rcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMaxu (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := rcastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hMaxuType : maxuOp.getOpType! ctx₅.raw = .riscv .maxu := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hMaxu (operation := maxuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := maxuOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := maxuOp)]
  have hSubType : subOp.getOpType! ctx₅.raw = .riscv .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := subOp)]
  have hCastBackType : castBackOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hLCastOperands : lcastOp.getOperands! ctx₅.raw = #[lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMaxu (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := lcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastOperands : rcastOp.getOperands! ctx₅.raw = #[rhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMaxu (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := rcastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hMaxuOperands : maxuOp.getOperands! ctx₅.raw
      = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMaxu (operation := maxuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := maxuOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := maxuOp)]
  have hSubOperands : subOp.getOperands! ctx₅.raw
      = #[ValuePtr.opResult (maxuOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := subOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₅.raw = #[ValuePtr.opResult (subOp.getResult 0)] := by grind
  -- The cast-back op's result type is the integer type `i64`.
  have hCBType : ((op.getResult 0).get! ctx₄.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₄.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hSub
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hMaxu
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hRCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hLCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hLCastResTypes : lcastOp.getResultTypes! ctx₅.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMaxu (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := lcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
  have hRCastResTypes : rcastOp.getResultTypes! ctx₅.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMaxu (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := rcastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
  have hMaxuResTypes : maxuOp.getResultTypes! ctx₅.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hMaxu (operation := maxuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := maxuOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := maxuOp)]
  have hSubResTypes : subOp.getResultTypes! ctx₅.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := subOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₅.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  -- Interpretation tail: execute `interpretOpList [lcastOp, rcastOp, maxuOp, subOp, castBackOp]`
  -- in `state'`. The frame clauses carry earlier bindings across later steps.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hLCastType hLCastOperands hLCastResTypes hLVal'
  have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₅.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw rhs lcastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hRhsNeLCastRes i)
  have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
    rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hRCastType hRCastOperands hRCastResTypes hRVal₁
  -- `maxu`'s first operand is the `lcast` register; transport its value through the `rcast` step.
  have hLCastNotRCastRes :
      ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₅.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw
        (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.maxu r₂ r₁) (fun _ _ _ _ => rfl) hMaxuType hMaxuOperands
      hMaxuResTypes hLRes₂ hRes₂
  -- `sub`'s second operand is again the `rcast` register; transport it through the `maxu` step.
  have hRCastNotMaxuRes :
      ValuePtr.opResult (rcastOp.getResult 0) ∉ maxuOp.getResults! ctx₅.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw
        (ValuePtr.opResult (rcastOp.getResult 0)) maxuOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
    rw [hFrame₃ _ hRCastNotMaxuRes]; exact hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.sub r₂ r₁) (fun _ _ _ _ => rfl) hSubType hSubOperands
      hSubResTypes hRes₃ hRRes₃
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
    interpretOp_castBack_forward (state := s₄) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₄
  refine ⟨s₅, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, liftM, monadLift, MonadLift.monadLift,
      Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.sub (LLVM.Int.toReg yt)
          (Data.RISCV.maxu (LLVM.Int.toReg yt) (LLVM.Int.toReg xt))) 64)], ?_, ?_⟩
    · simp [hRes₅, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using usubSat_isRefinedBy_toInt_sub_maxu hxtRef hytRef⟩

end Veir
