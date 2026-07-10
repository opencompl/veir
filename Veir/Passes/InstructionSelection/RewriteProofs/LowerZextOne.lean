import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.LowerExt

namespace Veir

/-!
## Correctness of `zext_1_local`

`zext_1_local` lowers `llvm.zext %x : i1 to i64` to
`unrealized_conversion_cast` (to a register) → `riscv.andi _, 1` →
`unrealized_conversion_cast` (back to `i64`). It is a SelectionDAG pattern
(`Veir.Passes.InstructionSelection.RISCV64Sdag`): masking the low bit with `andi 1` realizes the
zero extension of an `i1`.

The proof follows the `lowerExtLocal` template (single-operand extension: cast → riscv op → cast
back) but for the concrete `i1 → i64` widths, and with the middle op an *immediate*-form
`riscv.andi` rather than a plain unary reg-to-reg op. The source-interpretation unfolding
(`matchExtOp_interpretOp_unfold`) and the data-level zero-extension refinement lemma
(`zextLike_isRefinedBy_toInt`) are both reused from `LowerExt.lean`; only the `andi`-specific value
characterisation below is new.
-/

/-- `riscv.andi _, 1` masks off all but the low bit, i.e. it is the zero extension of the low bit
    of its register operand. -/
theorem andi_one_val (r : Data.RISCV.Reg) :
    (Data.RISCV.andi (BitVec.ofInt 12 1) r).val
      = BitVec.setWidth 64 (BitVec.setWidth 1 r.val) := by
  veir_bv_decide

/-- Correctness of the `riscv.andi _, 1` lowering of an `llvm.zext` from `i1` to `i64`: the round
    trip `i1 → reg → andi 1 → i64` refines `llvm.zext`. (`xt` is the possibly-more-defined
    target-side value of the operand.) -/
theorem zext1_isRefinedBy_toInt_andi {nneg : Bool} {x xt : Data.LLVM.Int 1} (h : x ⊒ xt) :
    Data.LLVM.Int.zext x 64 nneg (by omega)
      ⊒ RISCV.Reg.toInt (Data.RISCV.andi (BitVec.ofInt 12 1) (LLVM.Int.toReg xt)) 64 :=
  zextLike_isRefinedBy_toInt (by omega) (by omega) andi_one_val h

/-- Interpreter computation fact for `riscv.andi` at the immediate `1`. -/
theorem andi_one_interpretOp' (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .andi (RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)))
        resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.andi (BitVec.ofInt 12 1) r)], mem, none)) := rfl

set_option maxHeartbeats 1000000 in
theorem zext_1_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps zext_1_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges zext_1_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds zext_1_local}
    {h₄ : LocalRewritePattern.ReturnValues zext_1_local} :
    LocalRewritePattern.PreservesSemantics zext_1_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, zext_1_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchZext op ctx.raw).isSome := by
    cases hM : matchZext op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operand, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchZext_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, opIntTy, retIntTy, hOperTy, hResTy, hWlt⟩ :=
    OperationPtr.Verified.llvm_zext opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type is the integer type `retIntTy`; resolve the type-destructuring match.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType retIntTy := by
    rw [hResTy]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The result-width guard fixes the result width to `i64` (the initial `simp` swapped the
  -- negated `if`, so the continue branch is first).
  peelSplittableCondition' [hBw64] hpattern
  -- The operand type is the integer type `opIntTy`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opIntTy := by
    rw [← hOperand0, hOperTy]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- The operand-width guard fixes the operand width to `i1`.
  peelSplittableCondition' [hBw1] hpattern
  -- The op's result types, as needed by the width-dependent source interpretation.
  have hResTypes : op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  -- Unfold the interpretation of the matched op: exposes the operand's value and its `zext`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .zext)
      (srcFn := fun x hw props => Data.LLVM.Int.zext x _ props.nneg hw)
      opInBounds hOpType hNumResults hOperands hProps hResTypes hWlt zext_interpretOp'
      hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is the zero extension of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the three op creations (cast to register, `andi`, cast back), transporting the operand's
  -- dominance fact `hDomCtx` all the way into `ctx₃` as `hDom₃`.
  peelOpCreation! hpattern ctx₁ castOp hCast hDomCtx hDom₁
  peelOpCreation! hpattern ctx₂ andiOp hAndi hDom₁ hDom₂
  peelOpCreation! hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
  cleanupHpattern hpattern
  -- Read the refined value `xt` of `operand` in the target state `state'`.
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtx hDom₃ vNotOp
  -- Normalise the operand/result bitwidths to the literals `1`/`64`.
  obtain ⟨obw⟩ := opIntTy; simp only at hBw1; subst hBw1
  obtain ⟨rbw⟩ := retIntTy; simp only at hBw64; subst hBw64
  -- Structural facts about the three created ops.
  have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hAndiType : andiOp.getOpType! ctx₃.raw = .riscv .andi := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
  have hAndiOperands : andiOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (andiOp.getResult 0)] := by grind
  have hAndiProps : andiOp.getProperties! ctx₃.raw (.riscv .andi)
      = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAndi (operation := andiOp)]
  have hCastResTypes : castOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAndi (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hAndiResTypes : andiOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := andiOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hAndi (operation := andiOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, (by grind)⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
  -- Interpretation tail: execute `interpretOpList [castOp, andiOp, castBackOp]` in `state'`.
  -- `castOp` reads `operand = .int 1 xt` and casts it to `.reg (toReg xt)`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  -- `andiOp` maps `.reg r` to `.reg (andi 1 r)`.
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := Data.RISCV.andi (BitVec.ofInt 12 1) (LLVM.Int.toReg xt))
      (fun rt bo mem => andi_one_interpretOp' _ rt bo mem)
      hAndiType hAndiProps hAndiOperands hAndiResTypes hRes₁
  -- `castBackOp` casts `.reg (andi 1 (toReg xt))` back to `.int 64 (toInt (andi 1 (toReg xt)) 64)`.
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · -- The list interpretation is the chain of the three op interpretations.
    simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 64
        (RISCV.Reg.toInt (Data.RISCV.andi (BitVec.ofInt 12 1) (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using zext1_isRefinedBy_toInt_andi hxtRef⟩

/--
info: 'Veir.zext_1_local_preservesSemantics' depends on axioms: [propext,
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
 andi_one_val._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms zext_1_local_preservesSemantics

end Veir
