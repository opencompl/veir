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
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas

namespace Veir

/-!
## Correctness of `ashr_local`

`llvm.ashr` on an `i8`/`i32`/`i64` integer lowers to two `unrealized_conversion_cast`s (operands to
registers) → an arithmetic-shift-right riscv op → `unrealized_conversion_cast` (back to the integer
type). The riscv op depends on the width: `riscv.sra` for `i64`, `riscv.sraw` for `i32` (word
arithmetic shift, sign-extending the 32-bit result), and, for `i8`, `riscv.sra` applied to a
`riscv.sextb`-sign-extended value (the register holds the operand *zero*-extended, so it must be
sign-extended to 64 bits before the arithmetic shift).

The three data-level refinement lemmas below are the arithmetic core; they close by `veir_bv_decide`
off the `@[veir_bv_normalize]` `getValue_ashr`/`isPoison_ashr` (which supply, for a non-poison
result, the shift value and `y < w`, so the register op's masked shift amount agrees with the LLVM
one).
-/

/-- Correctness of the `riscv.sra` lowering of a 64-bit `llvm.ashr`. (`xt`/`yt` are the
    possibly-more-defined target-side operand values.) -/
theorem ashr_isRefinedBy_toInt_sra {x y xt yt : Data.LLVM.Int 64} (exact : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.ashr x y exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.sraw` lowering of a 32-bit `llvm.ashr`. -/
theorem ashr_isRefinedBy_toInt_sraw {x y xt yt : Data.LLVM.Int 32} (exact : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.ashr x y exact
      ⊒ RISCV.Reg.toInt (Data.RISCV.sraw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32 := by
  revert h₁ h₂
  veir_bv_decide

/-- Correctness of the `riscv.sra (riscv.sextb ·)` lowering of an 8-bit `llvm.ashr`: the operand is
    held zero-extended in the register, so it is sign-extended (`sextb`) to 64 bits before the
    arithmetic shift. -/
theorem ashr_isRefinedBy_toInt_sra_sextb {x y xt yt : Data.LLVM.Int 8} (exact : Bool)
    (h₁ : x ⊒ xt) (h₂ : y ⊒ yt) :
    Data.LLVM.Int.ashr x y exact
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.sra (LLVM.Int.toReg yt) (Data.RISCV.sextb (LLVM.Int.toReg xt))) 8 := by
  revert h₁ h₂
  veir_bv_decide

set_option maxHeartbeats 4000000 in
theorem ashr_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps ashr_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges ashr_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds ashr_local}
    {h₄ : LocalRewritePattern.ReturnValues ashr_local} :
    LocalRewritePattern.PreservesSemantics ashr_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, ashr_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchAshr op ctx.raw).isSome := by
    cases hM : matchAshr op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchAshr_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_ashr opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Resolve the three type-destructuring matches, peel the three (identical) width guards.
  rw [hLhsType] at hpattern
  simp only [] at hpattern
  peelSplittableCondition [hBwL] hpattern
  rw [hRhsType] at hpattern
  simp only [] at hpattern
  peelSplittableCondition [hBwR] hpattern
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  peelSplittableCondition [hBw] hpattern
  -- Unfold the interpretation of the matched op.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .ashr)
      (srcFn := fun x y props => Data.LLVM.Int.ashr x y props.exact)
      opInBounds hOpType hNumResults hOperands hProps
      (fun bw x y props rt bo mem res h => by
        simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h; grind)
      hinterp hLhsType hRhsType
  subst hCf
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two casts (shared prefix of all three branches).
  peelOpCreation!₂ hpattern ctx₁ lcastOp hLCast hDomCtxL hDomL₁ hDomCtxR hDomR₁
  peelOpCreation!₂ hpattern ctx₂ rcastOp hRCast hDomL₁ hDomL₂ hDomR₁ hDomR₂
  have hLCastFresh : ¬ lcastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds lcastOp hLCast
  have hRhsIn : rhs.InBounds ctx.raw := by clear hpattern; grind
  have hRhsNeLCastRes : ∀ i, rhs ≠ ValuePtr.opResult (lcastOp.getResult i) := by
    intro i heq
    rw [heq] at hRhsIn
    rw [ValuePtr.inBounds_opResult] at hRhsIn
    obtain ⟨hIn, -⟩ := hRhsIn
    exact hLCastFresh hIn
  have hLCastNeRCast : lcastOp ≠ rcastOp := by clear hpattern; grind
  have hBwCases : intType.bitwidth = 8 ∨ intType.bitwidth = 32 ∨ intType.bitwidth = 64 := by omega
  rcases hBwCases with hbw | hbw | hbw
  · -- ============ i8 branch: cast → cast → sextb → sra → castBack ============
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation!₂ hpattern ctx₃ lsOp hLs hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelOpCreation!₂ hpattern ctx₄ sraOp hSra hDomL₃ hDomL₄ hDomR₃ hDomR₄
    peelOpCreation!₂ hpattern ctx₅ castBackOp hCastBack hDomL₄ hDomL₅ hDomR₄ hDomR₅
    cleanupHpattern hpattern
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₅ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₅ rNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hRCastNeLs : rcastOp ≠ lsOp := by grind
    have hLCastType : lcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hLs (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastType : rcastOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hLs (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hLsType : lsOp.getOpType! ctx₅.raw = .riscv .sextb := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := lsOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hSraType : sraOp.getOpType! ctx₅.raw = .riscv .sra := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hCastBackType : castBackOp.getOpType! ctx₅.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₅.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₅.raw = #[rhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hLsOperands : lsOp.getOperands! ctx₅.raw = #[ValuePtr.opResult (lcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := lsOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hSraOperands : sraOp.getOperands! ctx₅.raw
        = #[ValuePtr.opResult (lsOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₅.raw = #[ValuePtr.opResult (sraOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₄.raw).type
        = (⟨Attribute.integerType { bitwidth := 8 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₄.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hSra
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLs
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRCast
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLCast
            (value := ValuePtr.opResult (op.getResult 0))]
      have h2 := hResType
      simp only [ValuePtr.getType!_opResult] at h1
      grind
    have hLCastResTypes : lcastOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastResTypes : rcastOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hLsResTypes : lsOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLs (operation := lsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := lsOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lsOp)]
    have hSraResTypes : sraOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSra (operation := sraOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sraOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₅.raw
        = #[⟨Attribute.integerType { bitwidth := 8 }, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₅.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 8 yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
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
      interpretOp_riscv_unaryReg_forward (state := s₂) (inBounds := by grind)
        (f := Data.RISCV.sextb) (fun _ _ _ _ => rfl) hLsType hLsOperands hLsResTypes hLRes₂
    have hRCastNotLsRes :
        ValuePtr.opResult (rcastOp.getResult 0) ∉ lsOp.getResults! ctx₅.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₅.raw
          (ValuePtr.opResult (rcastOp.getResult 0)) lsOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ hRCastNotLsRes]; exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
        (f := fun r₁ r₂ => Data.RISCV.sra r₂ r₁) (fun _ _ _ _ => rfl)
        hSraType hSraOperands hSraResTypes hRes₃ hRRes₃
    obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
      interpretOp_castBack_forward (state := s₄) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₄
    refine ⟨s₅, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · refine ⟨#[RuntimeValue.int 8
          (RISCV.Reg.toInt
            (Data.RISCV.sra (LLVM.Int.toReg yt) (Data.RISCV.sextb (LLVM.Int.toReg xt))) 8)], ?_, ?_⟩
      · simp [hRes₅, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using ashr_isRefinedBy_toInt_sra_sextb props.exact hxtRef hytRef⟩
  · -- ================= i32 branch: cast → cast → sraw → castBack =================
    rw [if_neg (show ¬intType.bitwidth = 8 by omega), if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelOpCreation!₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
    cleanupHpattern hpattern
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₄ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₄ rNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv .sraw := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₄.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₄.raw = #[rhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetOperands : retOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRCast
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLCast
            (value := ValuePtr.opResult (op.getResult 0))]
      have h2 := hResType
      simp only [ValuePtr.getType!_opResult] at h1
      grind
    have hLCastResTypes : lcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastResTypes : rcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 32 yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    have hLCastNotRCastRes :
        ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
          (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
        (f := fun r₁ r₂ => Data.RISCV.sraw r₂ r₁) (fun _ _ _ _ => rfl)
        hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32
          (RISCV.Reg.toInt (Data.RISCV.sraw (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 32)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using ashr_isRefinedBy_toInt_sraw props.exact hxtRef hytRef⟩
  · -- ================= i64 branch: cast → cast → sra → castBack =================
    rw [if_neg (show ¬intType.bitwidth = 8 by omega),
      if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelOpCreation!₂ hpattern ctx₃ retOp hRet hDomL₂ hDomL₃ hDomR₂ hDomR₃
    peelOpCreation!₂ hpattern ctx₄ castBackOp hCastBack hDomL₃ hDomL₄ hDomR₃ hDomR₄
    cleanupHpattern hpattern
    obtain ⟨xt, hLVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtxL hDomL₄ lNotOp
    obtain ⟨yt, hRVal', hytRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hyVal
        hDomCtxR hDomR₄ rNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hLCastType : lcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastType : rcastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetType : retOp.getOpType! ctx₄.raw = .riscv .sra := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hLCastOperands : lcastOp.getOperands! ctx₄.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastOperands : rcastOp.getOperands! ctx₄.raw = #[rhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetOperands : retOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (lcastOp.getResult 0), ValuePtr.opResult (rcastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRet (operation := retOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := retOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (retOp.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRet
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRCast
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hLCast
            (value := ValuePtr.opResult (op.getResult 0))]
      have h2 := hResType
      simp only [ValuePtr.getType!_opResult] at h1
      grind
    have hLCastResTypes : lcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := lcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := lcastOp)]
    have hRCastResTypes : rcastOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRCast (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := rcastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rcastOp)]
    have hRetResTypes : retOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := retOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRet (operation := retOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hLCastType hLCastOperands hLCastResTypes hLVal'
    have hRhsNotLCastRes : rhs ∉ lcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw rhs lcastOp
        with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (hRhsNeLCastRes i)
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int 64 yt) := by
      rw [hFrame₁ rhs hRhsNotLCastRes]; exact hRVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    have hLCastNotRCastRes :
        ValuePtr.opResult (lcastOp.getResult 0) ∉ rcastOp.getResults! ctx₄.raw := by
      rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
          (ValuePtr.opResult (lcastOp.getResult 0)) rcastOp with hres | ⟨i, hi, heq⟩
      · exact hres
      · exact absurd heq (by grind [OperationPtr.getResult])
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ hLCastNotRCastRes]; exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
        (f := fun r₁ r₂ => Data.RISCV.sra r₂ r₁) (fun _ _ _ _ => rfl)
        hRetType hRetOperands hRetResTypes hLRes₂ hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg yt) (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using ashr_isRefinedBy_toInt_sra props.exact hxtRef hytRef⟩

/--
info: 'Veir.ashr_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 ashr_isRefinedBy_toInt_sra._native.bv_decide.ax_1_5,
 ashr_isRefinedBy_toInt_sra_sextb._native.bv_decide.ax_1_5,
 ashr_isRefinedBy_toInt_sraw._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms ashr_local_preservesSemantics

end Veir
