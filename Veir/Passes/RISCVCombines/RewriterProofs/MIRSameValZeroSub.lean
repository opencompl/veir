import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.Casting
import Veir.Passes.RISCVCombines.MIRCombinesVeir
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.RISCVCombines.RewriterProofs.CommonConstantForward
import Veir.Passes.RISCVCombines.RewriterProofs.CommonMIRMatchEqns

namespace Veir

/-! ## Correctness of `same_val_zero_0_local` (`llvm.sub x x` → `llvm.mlir.constant 0`)

The sibling of `same_val_zero_1` (see `MIRSameValZeroXor.lean`), matching `llvm.sub` instead of
`llvm.xor`. `sub x x` is `0` (the subtraction never overflows, whatever `nsw`/`nuw` say), so the
structure — and proof — is identical to the `xor` case, only the matcher, verifier lemma, and data
lemma change. Both share `interpretOp_llvm_constant_forward` (`CommonConstantForward.lean`). -/

/-- The Layer-0 data refinement (at the `i64` width the combine fires on): `sub x x` (poison when
`x` is poison, else `0`, for any `nsw`/`nuw`) is refined by the constant `0`. -/
theorem sub_self_isRefinedBy_constant_zero (x : Data.LLVM.Int 64) (nsw nuw : Bool) :
    Data.LLVM.Int.sub x x nsw nuw ⊒ Data.LLVM.Int.constant 64 0 := by
  cases nsw <;> cases nuw <;> veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Correctness of the `same_val_zero_0_local` lowering: a 64-bit `llvm.sub x x` lowers to a single
`llvm.mlir.constant 0` of the `i64` result type, which refines the `sub`. -/
theorem same_val_zero_0_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics RISCV.same_val_zero_0_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, RISCV.same_val_zero_0_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch reaches the `some (...)` RHS.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, x1, xprops⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic + verification facts.
  have ⟨hOpType, hNRes, hOperands, hProps⟩ := matchSub_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by clear hpattern; grind
  have hVer := OperationPtr.Verified.llvm_sub opVerif hOpType
  obtain ⟨hNResV, hNOper, hNSucc, hNReg, intType, hResTy, hOp0Ty, hOp1Ty⟩ := hVer
  -- The `x != x1` guard is false, so the two operands are equal.
  have hResTyVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResTy]
  have hxx1 : x = x1 := by
    rcases Decidable.em (x = x1) with heq | hne
    · exact heq
    · rw [if_neg hne] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hxx1] at hpattern
  -- Resolve the result-type destructuring match: the result type is `integerType intType`.
  rw [hResTyVal] at hpattern
  simp only [] at hpattern
  -- The `bitwidth ≠ 64` guard is false, so the result width is 64.
  have hBw64 : intType.bitwidth = 64 := by
    rcases Decidable.em (intType.bitwidth = 64) with hbw | hbw
    · exact hbw
    · rw [if_neg hbw] at hpattern
      exact absurd hpattern (by simp)
  rw [if_pos hBw64] at hpattern
  -- The operands have integer type `intType`, feeding the source-interpretation unfolder.
  have hx0 : op.getOperand! ctx.raw 0 = x := by
    have : (op.getOperands! ctx.raw)[0]! = x := by rw [hOperands]; rfl
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hx1 : op.getOperand! ctx.raw 1 = x1 := by
    have : (op.getOperands! ctx.raw)[1]! = x1 := by rw [hOperands]; rfl
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hx0, hOp0Ty]
  have hRhsType : (x1.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hx1, hOp1Ty]
  -- Source value: `op`'s single result is `sub xv x1v props.nsw props.nuw`.
  obtain ⟨xv, x1v, hxVal, hx1Val, hMemEq, hResVal, rfl⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b props => Data.LLVM.Int.sub a b props.nsw props.nuw)
      (props := xprops) opInBounds hOpType hNRes hOperands hProps
      (by intro bw a b props resultTypes blockOperands mem res hI
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hI
          grind)
      hinterp hLhsType hRhsType
  -- The two operands are the same value, so `xv = x1v`.
  have hxvEq : xv = x1v := by
    rw [hxx1] at hxVal; rw [hxVal] at hx1Val; simpa using hx1Val
  subst hxvEq
  -- Source values array: `op`'s single result value is `sub xv xv props.nsw props.nuw`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the single created op: the `llvm.mlir.constant`.
  peelOpCreation hpattern ctx₁ cstOp hCst
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hCst
  cleanupHpattern hpattern
  -- Structural facts about the created constant op in the final context `ctx₁`.
  have hCstType : cstOp.getOpType! ctx₁.raw = .llvm .mlir__constant := by grind
  have hCstOperands : cstOp.getOperands! ctx₁.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCst (operation := cstOp)]
  have hCstProps : (cstOp.getProperties! ctx₁.raw (.llvm .mlir__constant)).value
      = .integer (IntegerAttr.mk 0 intType) := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hCst (operation := cstOp)]
  have hCstResTypes : cstOp.getResultTypes! ctx₁.raw
      = #[⟨Attribute.integerType intType, (by grind)⟩] := by
    have hty : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType intType, by grind⟩ :=
      Subtype.ext hResTyVal
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCst (operation := cstOp)]
  -- Interpretation tail: execute `interpretOpList [cstOp]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCstType hCstProps hCstOperands hCstResTypes
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.constant intType.bitwidth (IntegerAttr.mk 0 intType).value)], ?_, ?_⟩
    · simp [hRes₁, Option.bind, Option.map]
    · refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
      -- The result width is 64, so the concrete-width data lemma applies.
      clear hxVal hx1Val hResVal
      revert xv
      rw [hBw64]
      intro xv
      simpa using sub_self_isRefinedBy_constant_zero xv xprops.nsw xprops.nuw

/-- info: 'Veir.same_val_zero_0_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominatesIp,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 ValuePtr.dominatesIp,
 MemoryState.llvmLoad._native.bv_decide.ax_8] -/
#guard_msgs in
#print axioms same_val_zero_0_local_preservesSemantics

end Veir
