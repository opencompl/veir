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
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW

namespace Veir

/-!
## Correctness of `abs_local`

`llvm.intr.abs` on a 64-bit integer is lowered to
`unrealized_conversion_cast` (to a register) → `riscv.neg` → `riscv.max` (of the original register and
its negation) → `unrealized_conversion_cast` (back to the integer type), mirroring LLVM's RV64+Zbb
`neg`/`max` expansion of `abs`.

`abs` does not fit `lowerUnaryWLocal`: it is `i64`-only and emits *two* register ops whose second
(`max`) is a binary op consuming both the cast register and the `neg` result. It is therefore proven
bespoke; structurally it is the `lowerUnaryWLocal`/`bswap` `i64` shape with an extra
`interpretOp_riscv_unaryReg_forward` (`neg`) step and a `interpretOp_riscv_binaryReg_forward` (`max`)
step in place of the single unary-register forward step.
-/

/-- Correctness of the `max (neg ·) ·` lowering of a 64-bit `llvm.intr.abs`: the round trip
    `int → reg → neg/max → int` refines `abs`. (`xt` is the possibly-more-defined target-side value
    of the operand; `b` is the intrinsic's `is_int_min_poison` flag, which the lowering ignores: the
    `neg` wraps `intMin` back to `intMin`, so both the poison and non-poison forms are refined.) -/
theorem abs_isRefinedBy_toInt_max_neg {x xt : Data.LLVM.Int 64} {b : Bool} (h : x ⊒ xt) :
    Data.LLVM.Int.abs x b ⊒
      RISCV.Reg.toInt
        (Data.RISCV.max (Data.RISCV.neg (LLVM.Int.toReg xt)) (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_abs] at hnp; grind
  have hvd : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Correctness of the `abs_local` lowering: the `castToReg → neg → max → castBack` round trip
    refines `llvm.intr.abs`. -/
theorem abs_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics abs_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, abs_local, createRISCVUnitLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchAbs op ctx.raw).isSome := by
    cases hM : matchAbs op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨operand, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchAbs_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, hResOperType, intType, isT, hResType⟩ :=
    OperationPtr.Verified.llvm_intr__abs opVerif hOpType
  -- The operand type is the integer type `intType`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [show operand.getType! ctx.raw = ⟨.integerType intType, isT⟩ from by grind]
  -- The bitwidth guard matches on the *result* type; resolve it too.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand's value and `abs`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchUnaryOp_interpretOp_unfold
      (srcFn := fun {_} x props => Data.LLVM.Int.abs x props.is_int_min_poison)
      (props := op.getProperties! ctx.raw (.llvm .intr__abs))
      opInBounds hOpType hNumResults hOperands rfl (fun _ _ _ _ _ _ => rfl) hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition' [hBw] hpattern
  -- Source value: `op`'s single result is `abs` of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the `castToReg`, `neg`, `max`, and `castBack` creations.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtx hDom₁
  peelOpCreation! hpattern ctx₂ negOp hNeg hDom₁ hDom₂
  peelOpCreation! hpattern ctx₃ maxOp hMax hDom₂ hDom₃
  peelReplaceWithRegLocal hpattern ctx₄ castBackOp hCastBack hDom₃ hDom₄
  cleanupHpattern hpattern
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtx hDom₄ vNotOp
  obtain ⟨bw⟩ := intType; simp only at hBw; subst hBw
  have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
  have hNegType : negOp.getOpType! ctx₄.raw = .riscv .neg := by grind
  have hMaxType : maxOp.getOpType! ctx₄.raw = .riscv .max := by grind
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₄.raw = #[operand] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hNeg (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMax (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hNegOperands :
      negOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNeg (operation := negOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMax (operation := negOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := negOp)]
  have hMaxOperands :
      maxOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (castOp.getResult 0), ValuePtr.opResult (negOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMax (operation := maxOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := maxOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (maxOp.getResult 0)] := by grind
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hMax
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hNeg
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hCastResTypes : castOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hNeg (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMax (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hNegResTypes : negOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hNeg (operation := negOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hMax (operation := negOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := negOp)]
  have hMaxResTypes : maxOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hMax (operation := maxOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := maxOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hOther₂⟩ :=
    interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
      (f := Data.RISCV.neg) (fun _ _ _ _ => rfl) hNegType hNegOperands hNegResTypes hRes₁
  -- `max`'s first operand is the cast register (`castOp`'s result); transport its value from `s₁`
  -- through the `neg` step (`s₂`), which does not touch it since `castOp ≠ negOp`.
  have hCastNotNegRes : ValuePtr.opResult (castOp.getResult 0) ∉ negOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
        (ValuePtr.opResult (castOp.getResult 0)) negOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  have hCastRes₂ : s₂.variables.getVar? (ValuePtr.opResult (castOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
    rw [hOther₂ _ hCastNotNegRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.max r₂ r₁) (fun _ _ _ _ => rfl) hMaxType hMaxOperands
      hMaxResTypes hCastRes₂ hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt
        (Data.RISCV.max (Data.RISCV.neg (LLVM.Int.toReg xt)) (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using abs_isRefinedBy_toInt_max_neg hxtRef⟩

end Veir
