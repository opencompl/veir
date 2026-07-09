import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.Casting
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.CastsReconciliation.RewriteProofs.CommonCast
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret

namespace Veir

/-! ## Correctness of `reconcileRegIntCastLocal`

`reg -> iX -> reg` keeps only the low `X` bits of the register: `Reg.toInt` truncates and
`Int.toReg` zero-extends back, and no poison is ever involved (`Reg.toInt` is never poison). The
rewrite replaces the round trip by the RISC-V instruction that computes that zero-extension:
`zext.b`/`zext.h`/`zext.w` at `X = 8/16/32`, and an `slli`/`srli` pair by `64 - X` otherwise.

`X = 0` is excluded by the pattern: the round trip is then the constant zero, while the shift pair
would wrap its 6-bit shift amount `64 - 0` back to `0` and return the register unchanged. -/

/-! ### Data lemmas: the round trip is the zero-extension of the low word -/

theorem toReg_toInt_zextb {r : Data.RISCV.Reg} :
    LLVM.Int.toReg (RISCV.Reg.toInt r 8) = Data.RISCV.zextb r := by
  simp [LLVM.Int.toReg, RISCV.Reg.toInt, Data.RISCV.zextb, Data.RISCV.andi]
  bv_decide

theorem toReg_toInt_zexth {r : Data.RISCV.Reg} :
    LLVM.Int.toReg (RISCV.Reg.toInt r 16) = Data.RISCV.zexth r := by
  simp [LLVM.Int.toReg, RISCV.Reg.toInt, Data.RISCV.zexth]
  bv_decide

theorem toReg_toInt_zextw {r : Data.RISCV.Reg} :
    LLVM.Int.toReg (RISCV.Reg.toInt r 32) = Data.RISCV.zextw r := by
  simp [LLVM.Int.toReg, RISCV.Reg.toInt, Data.RISCV.zextw, Data.RISCV.adduw, Data.RISCV.li]
  bv_decide

/-- Shifting a 64-bit word left by `64 - bw` and back right (logically) keeps exactly its low `bw`
bits. `bw` is symbolic, so this is a bitwise argument rather than a `bv_decide`. -/
theorem BitVec.shiftLeft_ushiftRight_eq_setWidth {bw : Nat} (h0 : 0 < bw) (h : bw < 64)
    (x : BitVec 64) :
    (x <<< (BitVec.ofNat 6 (64 - bw))) >>> (BitVec.ofNat 6 (64 - bw))
      = (x.setWidth bw).setWidth 64 := by
  have hk : (BitVec.ofNat 6 (64 - bw)).toNat = 64 - bw := by
    simp [BitVec.toNat_ofNat]; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hib : i < bw
  · simp [hib, hi, hk]; omega
  · simp [hib, hi, hk]; omega

/-- The `slli`/`srli` form of the `reg -> iX -> reg` round trip, for `0 < X < 64`. The shift amount
is the immediate as the interpreter reads it (`BitVec.ofInt 6`). -/
theorem toReg_toInt_slli_srli {bw : Nat} (h0 : 0 < bw) (h : bw < 64) {r : Data.RISCV.Reg} :
    LLVM.Int.toReg (RISCV.Reg.toInt r bw)
      = Data.RISCV.srli (BitVec.ofInt 6 (64 - (bw : Int)))
          (Data.RISCV.slli (BitVec.ofInt 6 (64 - (bw : Int))) r) := by
  have himm : BitVec.ofInt 6 (64 - (bw : Int)) = BitVec.ofNat 6 (64 - bw) := by
    rw [show ((64 : Int) - (bw : Int)) = ((64 - bw : Nat) : Int) by omega]
    simp [BitVec.ofInt_natCast]
  simp only [himm, LLVM.Int.toReg, RISCV.Reg.toInt, Data.RISCV.srli, Data.RISCV.slli,
    BitVec.truncate_eq_setWidth]
  rw [BitVec.shiftLeft_ushiftRight_eq_setWidth h0 h]

/-! ### Interpreter computation facts for the emitted ops -/

theorem zextb_interpretOp' (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf Riscv.zextb)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .zextb props resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.zextb r)], mem, none)) := rfl

theorem zexth_interpretOp' (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf Riscv.zexth)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .zexth props resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.zexth r)], mem, none)) := rfl

theorem zextw_interpretOp' (r : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf Riscv.zextw)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .zextw props resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.zextw r)], mem, none)) := rfl

theorem slli_interpretOp' (r : Data.RISCV.Reg) (imm : IntegerAttr)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .slli (RISCVImmediateProperties.mk imm) resultTypes #[.reg r]
        blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.slli (BitVec.ofInt 6 imm.value) r)], mem, none)) := rfl

theorem srli_interpretOp' (r : Data.RISCV.Reg) (imm : IntegerAttr)
    (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .srli (RISCVImmediateProperties.mk imm) resultTypes #[.reg r]
        blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.srli (BitVec.ofInt 6 imm.value) r)], mem, none)) := rfl

set_option maxHeartbeats 4000000 in
theorem reconcileRegIntCastLocal_preservesSemantics :
    LocalRewritePattern.PreservesSemantics reconcileRegIntCastLocal h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, reconcileRegIntCastLocal]
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
  -- The operand must be defined by an operation.
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
  -- Peel the two type guards.
  have hTyEq : ((op.getResult 0).get! ctx.raw).type = parentInput.getType! ctx.raw := by
    rcases Decidable.em (((op.getResult 0).get! ctx.raw).type = parentInput.getType! ctx.raw)
      with hty | hty
    · exact hty
    · rw [if_neg hty] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hTyEq] at hpattern
  have hRegTy : parentInput.getType! ctx.raw = (RegisterType.mk : TypeAttr) := by
    rcases Decidable.em (parentInput.getType! ctx.raw = (RegisterType.mk : TypeAttr)) with hty | hty
    · exact hty
    · rw [if_neg hty] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hRegTy] at hpattern
  -- The intermediate type must be an integer type.
  obtain ⟨bw, hbw⟩ :
      ∃ bw, ((ValuePtr.opResult castPtr).getType! ctx.raw).val = .integerType ⟨bw⟩ := by
    cases hty : ((ValuePtr.opResult castPtr).getType! ctx.raw).val
    case integerType it => cases it; exact ⟨_, rfl⟩
    all_goals (rw [hty] at hpattern; simp at hpattern)
  rw [hbw] at hpattern
  simp only [] at hpattern
  -- Syntactic facts from the outer match.
  obtain ⟨hOpType, hNRes, hOperands⟩ := matchCastOp_implies hMatch
  have hOperandMem : ValuePtr.opResult castPtr ∈ op.getOperands! ctx.raw := by
    rw [hOperands]; simp
  have hResults : op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] := by
    clear hpattern; grind
  -- Source side: the outer cast reads the inner cast's value and casts it back to a register.
  obtain ⟨w, u, hInputVal, hCastOuter, hMemEq, hResVal, rfl⟩ :=
    castOp_interpretOp_unfold opInBounds hOpType hNRes hOperands rfl hinterp
  obtain ⟨v, w', hParentVal, hCastInner, hInputVal', hParentDom, hParentIn, hParentNotRes⟩ :=
    castOp_getVar?_of_EquationLemmaAt ctxDom opInBounds stateWf hMatch' hOperandMem
  have hww : w' = w := by rw [hInputVal'] at hInputVal; simpa using hInputVal
  rw [hww] at hCastInner
  -- The parent's value is a register `r`.
  have hConf : v.Conforms (parentInput.getType! ctx.raw) := VariableState.getVar?_conforms hParentVal
  rw [hRegTy] at hConf
  obtain ⟨r, rfl⟩ := RuntimeValue.Conforms.registerType hConf
  -- The inner cast truncates it to `i{bw}`, the outer one zero-extends it back.
  rw [show (ValuePtr.opResult castPtr).getType! ctx.raw
      = ⟨.integerType ⟨bw⟩, hbw ▸ ((ValuePtr.opResult castPtr).getType! ctx.raw).2⟩
      from Subtype.ext hbw] at hCastInner
  simp only [castRuntimeValue, Option.some.injEq] at hCastInner
  subst hCastInner
  rw [hTyEq, hRegTy] at hCastOuter
  simp only [castRuntimeValue, Option.some.injEq] at hCastOuter
  subst hCastOuter
  -- Source values: `op`'s single result holds the round trip's value.
  rw [hResults] at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Split on the intermediate bitwidth: `8`/`16`/`32` emit one op, the rest emit `slli`+`srli`.
  split at hpattern
  · -- `bw = 8`: `zext.b`
    peelOpCreation! hpattern ctx₁ zextOp hZext hParentDom hDom₁
    cleanupHpattern hpattern
    have hZextType : zextOp.getOpType! ctx₁.raw = .riscv .zextb := by grind
    have hZextOperands : zextOp.getOperands! ctx₁.raw = #[parentInput] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hZext (operation := zextOp)]
    have hZextResTypes : zextOp.getResultTypes! ctx₁.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hZext (operation := zextOp)]
    obtain ⟨tv, hTvVal, hTvRef⟩ :=
      LocalRewritePattern.exists_refined_getVar? valueRefinement state'Dom hParentIn hParentVal
        hParentDom hDom₁ hParentNotRes
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hTvRef
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := state') (inBounds := by grind)
        (f := Data.RISCV.zextb) (fun props rt bo mem => zextb_interpretOp' _ props rt bo mem)
        hZextType hZextOperands hZextResTypes hTvVal
    refine ⟨s₁, by simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp],
      by grind, ?_⟩
    refine ⟨#[RuntimeValue.reg (Data.RISCV.zextb r)], by simp [hRes₁, Option.bind, Option.map], ?_⟩
    exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
      (by simp [RuntimeValue.isRefinedBy, toReg_toInt_zextb])
  · -- `bw = 16`: `zext.h`
    peelOpCreation! hpattern ctx₁ zextOp hZext hParentDom hDom₁
    cleanupHpattern hpattern
    have hZextType : zextOp.getOpType! ctx₁.raw = .riscv .zexth := by grind
    have hZextOperands : zextOp.getOperands! ctx₁.raw = #[parentInput] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hZext (operation := zextOp)]
    have hZextResTypes : zextOp.getResultTypes! ctx₁.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hZext (operation := zextOp)]
    obtain ⟨tv, hTvVal, hTvRef⟩ :=
      LocalRewritePattern.exists_refined_getVar? valueRefinement state'Dom hParentIn hParentVal
        hParentDom hDom₁ hParentNotRes
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hTvRef
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := state') (inBounds := by grind)
        (f := Data.RISCV.zexth) (fun props rt bo mem => zexth_interpretOp' _ props rt bo mem)
        hZextType hZextOperands hZextResTypes hTvVal
    refine ⟨s₁, by simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp],
      by grind, ?_⟩
    refine ⟨#[RuntimeValue.reg (Data.RISCV.zexth r)], by simp [hRes₁, Option.bind, Option.map], ?_⟩
    exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
      (by simp [RuntimeValue.isRefinedBy, toReg_toInt_zexth])
  · -- `bw = 32`: `zext.w`
    peelOpCreation! hpattern ctx₁ zextOp hZext hParentDom hDom₁
    cleanupHpattern hpattern
    have hZextType : zextOp.getOpType! ctx₁.raw = .riscv .zextw := by grind
    have hZextOperands : zextOp.getOperands! ctx₁.raw = #[parentInput] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hZext (operation := zextOp)]
    have hZextResTypes : zextOp.getResultTypes! ctx₁.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hZext (operation := zextOp)]
    obtain ⟨tv, hTvVal, hTvRef⟩ :=
      LocalRewritePattern.exists_refined_getVar? valueRefinement state'Dom hParentIn hParentVal
        hParentDom hDom₁ hParentNotRes
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hTvRef
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := state') (inBounds := by grind)
        (f := Data.RISCV.zextw) (fun props rt bo mem => zextw_interpretOp' _ props rt bo mem)
        hZextType hZextOperands hZextResTypes hTvVal
    refine ⟨s₁, by simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp],
      by grind, ?_⟩
    refine ⟨#[RuntimeValue.reg (Data.RISCV.zextw r)], by simp [hRes₁, Option.bind, Option.map], ?_⟩
    exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
      (by simp [RuntimeValue.isRefinedBy, toReg_toInt_zextw])
  · -- otherwise: `slli` then `srli` by `64 - bw`, for `0 < bw < 64`.
    have hbw0 : bw ≠ 0 := by
      intro hz; rw [hz] at hpattern; simp at hpattern
    rw [if_neg hbw0] at hpattern
    have hbwlt : ¬ (64 ≤ bw) := by
      intro hge; rw [if_pos hge] at hpattern; simp at hpattern
    rw [if_neg hbwlt] at hpattern
    peelOpCreation! hpattern ctx₁ shlOp hShl hParentDom hDom₁
    peelOpCreation! hpattern ctx₂ srlOp hSrl hDom₁ hDom₂
    cleanupHpattern hpattern
    have hShlType : shlOp.getOpType! ctx₂.raw = .riscv .slli := by grind
    have hSrlType : srlOp.getOpType! ctx₂.raw = .riscv .srli := by grind
    have hShlOperands : shlOp.getOperands! ctx₂.raw = #[parentInput] := by grind
    have hSrlOperands : srlOp.getOperands! ctx₂.raw
        = #[ValuePtr.opResult (shlOp.getResult 0)] := by grind
    have hShlProps : shlOp.getProperties! ctx₂.raw (.riscv .slli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (64 - (bw : Int)) (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSrl (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hShl (operation := shlOp)]
    have hSrlProps : srlOp.getProperties! ctx₂.raw (.riscv .srli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (64 - (bw : Int)) (IntegerType.mk 64)) := by
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSrl (operation := srlOp)]
    have hShlResTypes : shlOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hShl (operation := shlOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := shlOp)]
    have hSrlResTypes : srlOp.getResultTypes! ctx₂.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSrl (operation := srlOp)]
    obtain ⟨tv, hTvVal, hTvRef⟩ :=
      LocalRewritePattern.exists_refined_getVar? valueRefinement state'Dom hParentIn hParentVal
        hParentDom hDom₂ hParentNotRes
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hTvRef
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := state') (inBounds := by grind)
        (res := Data.RISCV.slli (BitVec.ofInt 6 (64 - (bw : Int))) r)
        (fun rt bo mem => slli_interpretOp' _ _ rt bo mem)
        hShlType hShlProps hShlOperands hShlResTypes hTvVal
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := Data.RISCV.srli (BitVec.ofInt 6 (64 - (bw : Int)))
          (Data.RISCV.slli (BitVec.ofInt 6 (64 - (bw : Int))) r))
        (fun rt bo mem => srli_interpretOp' _ _ rt bo mem)
        hSrlType hSrlProps hSrlOperands hSrlResTypes hRes₁
    refine ⟨s₂, by simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift,
      Interp], by grind, ?_⟩
    refine ⟨#[RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 (64 - (bw : Int)))
      (Data.RISCV.slli (BitVec.ofInt 6 (64 - (bw : Int))) r))],
      by simp [hRes₂, Option.bind, Option.map], ?_⟩
    exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
      (by simp [RuntimeValue.isRefinedBy,
        toReg_toInt_slli_srli (Nat.pos_of_ne_zero hbw0) (by omega)])

/-- info: 'Veir.reconcileRegIntCastLocal_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 ValuePtr.dominatesIp_before_of_strictlyDominates,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 toReg_toInt_zextb._native.bv_decide.ax_1_11,
 MemoryState.llvmLoad._native.bv_decide.ax_8] -/
#guard_msgs in
#print axioms reconcileRegIntCastLocal_preservesSemantics

end Veir
