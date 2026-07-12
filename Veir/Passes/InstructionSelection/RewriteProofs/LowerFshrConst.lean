import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.Proofs
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect

namespace Veir

/-!
## Correctness of `fshrConst_local`

`llvm.intr.fshr a a (const)` with identical data operands and a constant shift amount is a constant
rotate-right. On `i64` it is lowered to `unrealized_conversion_cast` (value → register) →
`riscv.rori` (immediate form) → `unrealized_conversion_cast` (back to `i64`); on `i32` the exact
`roriw` shape of `roriw_local`.

This is the width-generic sibling of `roriw_local`: everything up to and including the value cast is
shared; the lowering then branches on `bitwidth = 32` (emitting `roriw`, whose refinement is
`fshr_roriw_const_isRefinedBy_toInt`) vs the `i64` case (emitting `rori`, refined by
`fshr_rori_const_isRefinedBy_toInt`). Both data-level refinements are discharged directly by
`veir_bv_decide` after normalizing the immediate to the low bits of the constant.
-/

/-- The data-level rotate refinement for the constant-amount i32 `fshr` lowering: a rotate-right by
    the constant `v` refines `roriw a, (v mod 32)` (five-bit immediate). The i32 analogue of
    `fshr_rori_const_isRefinedBy_toInt`. -/
theorem fshr_roriw_const_isRefinedBy_toInt {x xt : Data.LLVM.Int 32} (v : Int) (hx : x ⊒ xt) :
    Data.LLVM.Int.fshr x x (Data.LLVM.Int.constant 32 v)
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.roriw (BitVec.ofInt 5 (v % 32)) (LLVM.Int.toReg xt)) 32 := by
  rw [Data.RISCV.roriw,
    show BitVec.ofInt 5 (v % 32) = BitVec.setWidth 5 (BitVec.ofInt 32 v) from by
      rw [← BitVec.toNat_inj]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 32 v = c
  revert hx
  veir_bv_decide

/-- The data-level rotate refinement for the constant-amount i64 `fshr` lowering: a rotate-right by
    the constant `v` refines `rori a, (v mod 64)`, where the operand refinement `x ⊒ xt` threads the
    (possibly-more-defined) target-side value. The i64 analogue of
    `fshr_roriw_const_isRefinedBy_toInt` (six-bit immediate). -/
theorem fshr_rori_const_isRefinedBy_toInt {x xt : Data.LLVM.Int 64} (v : Int) (hx : x ⊒ xt) :
    Data.LLVM.Int.fshr x x (Data.LLVM.Int.constant 64 v)
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.rori (BitVec.ofInt 6 (v % 64)) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.RISCV.rori,
    show BitVec.ofInt 6 (v % 64) = BitVec.setWidth 6 (BitVec.ofInt 64 v) from by
      rw [← BitVec.toNat_inj]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 v = c
  revert hx
  veir_bv_decide

set_option maxHeartbeats 3200000 in
/-- Correctness of the `fshrConst_local` lowering: the `castToReg → rori/roriw (imm) → castBack`
    round trip refines `llvm.intr.fshr a a (const)` on `i64`/`i32`. -/
theorem fshrConst_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics fshrConst_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, fshrConst_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the `matchFshr` matcher.
  have hMatchSome : (matchFshr op ctx.raw).isSome := by
    cases hM : matchFshr op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchFshr_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    OperationPtr.Verified.llvm_intr__fshr opVerif hOpType
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hAmtEq : amt = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [hAmtEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, hOp2Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- The validity proof for the (integer) result type, reused for the fresh `TypeAttr`s below.
  have isT : Attribute.isType (Attribute.integerType intType) :=
    hResTypeVal ▸ (((op.getResult 0).get! ctx.raw).type).2
  -- The `a = b` guard: `simp` flipped `if a ≠ b then none` to `if a = b then _ else none`.
  have hAeqB : a = b := by
    rcases Decidable.em (a = b) with h | hne
    · exact h
    · rw [if_neg hne] at hpattern; simp at hpattern
  rw [if_pos hAeqB] at hpattern
  -- Peel the constant match on the shift amount.
  have hCVSome : (matchConstantIntVal amt ctx.raw).isSome := by
    cases hCV : matchConstantIntVal amt ctx.raw with
    | some y => rfl
    | none => rw [hCV] at hpattern; simp at hpattern
  obtain ⟨amtAttr, hCV⟩ := Option.isSome_iff_exists.mp hCVSome
  rw [hCV] at hpattern
  simp only [] at hpattern
  -- Resolve the result-type-destructuring match on `intType`.
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false (else the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Unfold the interpretation of the matched `fshr`: exposes the operand values and their `fshr`.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold (srcFn := fun {_} x y z => Data.LLVM.Int.fshr x y z)
      opInBounds hOpType hNumResults hOperands
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hinterp hAType hBType hAmtType
  subst hCf
  -- `a = b` gives `xa = xb`, so the source result `fshr xa xb xc` is the rotate `fshr xa xa xc`.
  have hxab : xa = xb := by
    have := haVal; rw [hAeqB] at this; rw [hbVal] at this; grind
  subst hxab
  -- Pin the shift amount's runtime value to the matched constant via `EquationLemmaAt`.
  have hcConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCV (by rw [hOperands]; simp) hAmtType
  obtain rfl : xc = Data.LLVM.Int.constant intType.bitwidth amtAttr.value := by
    have h := hcVal.symm.trans hcConst; simpa using h
  -- The value operand `a` dominates the rewrite point in the source context.
  have hDomCtxA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `fshr` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the shared value cast `castToReg a`.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtxA hDom₁
  -- Branch on the result bitwidth.
  obtain ⟨bw⟩ := intType
  by_cases hbw32 : bw = 32
  · -- i32: `roriw` (the `roriw_local` shape).
    subst hbw32
    simp only [↓reduceIte] at hpattern
    peelOpCreation! hpattern ctx₂ roriwOp hRoriw hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    -- Read the refined value `xt` of `a` in the target state `state'`.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomCtxA hDom₃ aNotOp
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRoriwType : roriwOp.getOpType! ctx₃.raw = .riscv .roriw := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[a] := by grind
    have hRoriwOperands :
        roriwOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRoriw (operation := roriwOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := roriwOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (roriwOp.getResult 0)] := by grind
    have hRoriwProps : roriwOp.getProperties! ctx₃.raw (.riscv .roriw)
        = RISCVImmediateProperties.mk
            (IntegerAttr.mk (amtAttr.value % 32) (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hRoriw (operation := roriwOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRoriw
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRoriw (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRoriwResTypes : roriwOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRoriw (operation := roriwOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := roriwOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := Data.RISCV.roriw (BitVec.ofInt 5 (amtAttr.value % 32))
          (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hRoriwType hRoriwProps hRoriwOperands hRoriwResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt
          (Data.RISCV.roriw (BitVec.ofInt 5 (amtAttr.value % 32))
            (LLVM.Int.toReg xt)) 32)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshr_roriw_const_isRefinedBy_toInt amtAttr.value hxtRef⟩
  · -- i64: `rori`.
    have hbw64 : bw = 64 := by simp only [] at hBw; omega
    subst hbw64
    rw [if_neg hbw32] at hpattern
    peelOpCreation! hpattern ctx₂ roriOp hRori hDom₁ hDom₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    -- Read the refined value `xt` of `a` in the target state `state'`.
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomCtxA hDom₃ aNotOp
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRoriType : roriOp.getOpType! ctx₃.raw = .riscv .rori := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[a] := by grind
    have hRoriOperands :
        roriOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (roriOp.getResult 0)] := by grind
    have hRoriProps : roriOp.getProperties! ctx₃.raw (.riscv .rori)
        = RISCVImmediateProperties.mk
            (IntegerAttr.mk (amtAttr.value % 64) (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hRori (operation := roriOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRori
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRoriResTypes : roriOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := Data.RISCV.rori (BitVec.ofInt 6 (amtAttr.value % 64))
          (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hRoriType hRoriProps hRoriOperands hRoriResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
          (Data.RISCV.rori (BitVec.ofInt 6 (amtAttr.value % 64))
            (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using fshr_rori_const_isRefinedBy_toInt amtAttr.value hxtRef⟩

end Veir
