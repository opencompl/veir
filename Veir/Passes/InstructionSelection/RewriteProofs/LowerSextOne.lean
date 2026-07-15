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
## Correctness of `sext_1_local`

`sext_1_local` lowers `llvm.sext %x : i1 to i64` (or `to i32`) to
`unrealized_conversion_cast` (to a register) → `riscv.slli _, 63` → `riscv.srai _, 63` →
`unrealized_conversion_cast` (back to the result type). It is a SelectionDAG pattern
(`Veir.Passes.InstructionSelection.RISCV64Sdag`): shifting the low bit to the top and then
arithmetic-shifting it back down splats the bit across the whole register, realizing the sign
extension of an `i1`.

The proof follows the `lowerExtLocal` template (single-operand extension) but for the concrete
`i1 → i64`/`i1 → i32` widths, with the two middle ops *immediate*-form `riscv.slli`/`riscv.srai`
rather than plain unary reg-to-reg ops. Crucially the emitted register chain is *identical* for both
result widths (`slli 63` then `srai 63` produces `0`/`-1`, which reads correctly as `0`/`-1` at
either 32 or 64 bits), so there is no bitwidth branch: the result width `retW ∈ {32, 64}` only enters
the final cast-back type and the width-generic refinement lemma. The source-interpretation unfolding
(`matchExtOp_interpretOp_unfold`) and the data-level sign-extension refinement lemma
(`sextLike_isRefinedBy_toInt`) are both reused from `LowerExt.lean`; only the `srai 63 ∘ slli 63`
value characterisation below is new.
-/

/-- `riscv.srai (riscv.slli r, 63), 63` splats the low bit of `r` across all 64 bits, i.e. it is the
    sign extension of the low bit of its register operand. -/
theorem srai_slli_63_val (r : Data.RISCV.Reg) :
    (Data.RISCV.srai (BitVec.ofInt 6 63) (Data.RISCV.slli (BitVec.ofInt 6 63) r)).val
      = BitVec.signExtend 64 (BitVec.setWidth 1 r.val) := by
  veir_bv_decide

/-- Correctness of the `srai (slli _ 63) 63` lowering of an `llvm.sext` from `i1` to `i{retW}`
    (`retW ∈ {32, 64}`): the round trip `i1 → reg → slli 63 → srai 63 → i{retW}` refines
    `llvm.sext`. (`xt` is the possibly-more-defined target-side value of the operand.) -/
theorem sext1_isRefinedBy_toInt_srai_slli {retW : Nat} (hlt : 1 < retW) (hle : retW ≤ 64)
    {x xt : Data.LLVM.Int 1} (h : x ⊒ xt) :
    Data.LLVM.Int.sext x retW hlt
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.srai (BitVec.ofInt 6 63)
            (Data.RISCV.slli (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))) retW :=
  sextLike_isRefinedBy_toInt (f := fun r => Data.RISCV.srai (BitVec.ofInt 6 63)
    (Data.RISCV.slli (BitVec.ofInt 6 63) r)) hlt hle srai_slli_63_val h

/-- Interpreter computation fact for `riscv.slli` at the immediate `63`. -/
theorem slli_63_interpretOp' (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .slli (RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 6)))
        resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.slli (BitVec.ofInt 6 63) r)], mem, none)) := rfl

/-- Interpreter computation fact for `riscv.srai` at the immediate `63`. -/
theorem srai_63_interpretOp' (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .srai (RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 6)))
        resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.srai (BitVec.ofInt 6 63) r)], mem, none)) := rfl

set_option maxHeartbeats 1000000 in
theorem sext_1_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sext_1_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sext_1_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sext_1_local}
    {h₄ : LocalRewritePattern.ReturnValues sext_1_local} :
    LocalRewritePattern.PreservesSemantics sext_1_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sext_1_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchSext op ctx.raw).isSome := by
    cases hM : matchSext op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operand, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchSext_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, opIntTy, retIntTy, hOperTy, hResTy, hWlt⟩ :=
    OperationPtr.Verified.llvm_sext opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type is the integer type `retIntTy`; resolve the type-destructuring match.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType retIntTy := by
    rw [hResTy]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- The result-width guard leaves `retW ∈ {32, 64}` (the bail branch is the `isTrue` arm).
  peelSplittableCondition [hW] hpattern
  have hRetLe : retIntTy.bitwidth ≤ 64 := by omega
  -- The operand type is the integer type `opIntTy`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opIntTy := by
    rw [← hOperand0, hOperTy]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- The operand-width guard fixes the operand width to `i1` (the initial `simp` swapped the
  -- negated `if`, so the continue branch is first).
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
  -- Unfold the interpretation of the matched op: exposes the operand's value and its `sext`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .sext)
      (srcFn := fun x hw _ => Data.LLVM.Int.sext x _ hw)
      opInBounds hOpType hNumResults hOperands hProps hResTypes hWlt sext_interpretOp'
      hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is the sign extension of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the four op creations (cast to register, `slli`, `srai`, cast back), transporting the
  -- operand's dominance fact `hDomCtx` all the way into `ctx₄` as `hDom₄`.
  peelOpCreation! hpattern ctx₁ castOp hCast hDomCtx hDom₁
  peelOpCreation! hpattern ctx₂ slliOp hSlli hDom₁ hDom₂
  peelOpCreation! hpattern ctx₃ sraiOp hSrai hDom₂ hDom₃
  peelOpCreation! hpattern ctx₄ castBackOp hCastBack hDom₃ hDom₄
  cleanupHpattern hpattern
  -- Read the refined value `xt` of `operand` in the target state `state'`.
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtx hDom₄ vNotOp
  -- Normalise the operand bitwidth to the literal `1`.
  obtain ⟨obw⟩ := opIntTy; simp only at hBw1; subst hBw1
  -- Structural facts about the four created ops.
  have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
  have hSlliType : slliOp.getOpType! ctx₄.raw = .riscv .slli := by grind
  have hSraiType : sraiOp.getOpType! ctx₄.raw = .riscv .srai := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSrai (operation := sraiOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := sraiOp)]
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₄.raw = #[operand] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSlli (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSrai (operation := castOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hSlliOperands : slliOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSlli (operation := slliOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSrai (operation := slliOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := slliOp)]
  have hSraiOperands : sraiOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (slliOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSrai (operation := sraiOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := sraiOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (sraiOp.getResult 0)] := by grind
  have hSlliProps : slliOp.getProperties! ctx₄.raw (.riscv .slli)
      = RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 6)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSrai (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSlli (operation := slliOp)]
  have hSraiProps : sraiOp.getProperties! ctx₄.raw (.riscv .srai)
      = RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 6)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSrai (operation := sraiOp)]
  have hCastResTypes : castOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSlli (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSrai (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hSlliResTypes : slliOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSlli (operation := slliOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hSrai (operation := slliOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := slliOp)]
  have hSraiResTypes : sraiOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSrai (operation := sraiOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := sraiOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType retIntTy, (by grind)⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castBackOp)]
  -- Interpretation tail: execute `interpretOpList [castOp, slliOp, sraiOp, castBackOp]` in `state'`.
  -- `castOp` reads `operand = .int 1 xt` and casts it to `.reg (toReg xt)`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  -- `slliOp` maps `.reg r` to `.reg (slli 63 r)`.
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := Data.RISCV.slli (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))
      (fun rt bo mem => slli_63_interpretOp' _ rt bo mem)
      hSlliType hSlliProps hSlliOperands hSlliResTypes hRes₁
  -- `sraiOp` maps `.reg r` to `.reg (srai 63 r)`.
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := by grind)
      (res := Data.RISCV.srai (BitVec.ofInt 6 63)
        (Data.RISCV.slli (BitVec.ofInt 6 63) (LLVM.Int.toReg xt)))
      (fun rt bo mem => srai_63_interpretOp' _ rt bo mem)
      hSraiType hSraiProps hSraiOperands hSraiResTypes hRes₂
  -- `castBackOp` casts the register back to `.int retW (toInt _ retW)`.
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · -- The list interpretation is the chain of the four op interpretations.
    simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.srai (BitVec.ofInt 6 63)
          (Data.RISCV.slli (BitVec.ofInt 6 63) (LLVM.Int.toReg xt))) retIntTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using sext1_isRefinedBy_toInt_srai_slli hWlt hRetLe hxtRef⟩

/--
info: 'Veir.sext_1_local_preservesSemantics' depends on axioms: [propext,
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
 srai_slli_63_val._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms sext_1_local_preservesSemantics

end Veir
