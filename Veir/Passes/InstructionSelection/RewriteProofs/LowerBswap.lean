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
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW

namespace Veir

/-!
## Correctness of `bswap_local`

`bswap_local` lowers `llvm.intr.bswap` on an `i64`/`i32` operand:
- `i64`: `unrealized_conversion_cast` (to a register) → `riscv.rev8` → `unrealized_conversion_cast`;
- `i32`: `unrealized_conversion_cast` → `riscv.rev8` → `riscv.srli _, 32` → `unrealized_conversion_cast`
  (`rev8` reverses all 8 bytes, landing the wanted low 4 bytes in the *high* word, so `srli 32`
  shifts them back down).

The proof follows the `lowerUnaryWLocal` template (single integer operand: cast → riscv op → cast
back), reusing `matchUnaryOp_interpretOp_unfold` from `LowerUnaryW.lean`. Unlike that combinator, the
two bitwidths take *different* op chains — three ops for `i64`, four for `i32` (an extra
immediate-form `riscv.srli`) — so the proof peels the shared `cast`/`rev8` prefix, `rcases` on the
bitwidth, and finishes each chain separately (the `i64` branch mirrors `lowerUnaryWLocal`, the `i32`
branch threads one extra `interpretOp_riscv_unaryReg_imm_forward` step). The two data-level
byte-reversal refinement lemmas below are the only genuinely new work.
-/

/-- Correctness of the `riscv.rev8` lowering of a 64-bit `llvm.intr.bswap`: the round trip
    `i64 → reg → rev8 → i64` refines `bswap`. (`xt` is the possibly-more-defined target-side value
    of the operand.) -/
theorem bswap_isRefinedBy_toInt_rev8 {x xt : Data.LLVM.Int 64} (h : x ⊒ xt) :
    Data.LLVM.Int.bswap x ⊒ RISCV.Reg.toInt (Data.RISCV.rev8 (LLVM.Int.toReg xt)) 64 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_bswap] at hnp; exact hnp
  have hvd : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.rev8]
  veir_bv_decide

/-- Correctness of the `srli (rev8 _) 32` lowering of a 32-bit `llvm.intr.bswap`: `rev8` reverses all
    eight bytes of the zero-extended register (landing the reversed low four bytes in the high word),
    and `srli 32` shifts them back into the low word. -/
theorem bswap_isRefinedBy_toInt_srli_rev8 {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.bswap x
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.srli (BitVec.ofInt 6 32) (Data.RISCV.rev8 (LLVM.Int.toReg xt))) 32 := by
  rw [Data.LLVM.Int.isRefinedBy_iff] at h ⊢
  obtain ⟨hp, hv⟩ := h
  refine ⟨fun _ => toInt_isPoison, fun hnp _ => ?_⟩
  have hxnp : x.isPoison = false := by
    rw [Data.LLVM.Int.isPoison_bswap] at hnp; exact hnp
  have hvd : x.getValueD = xt.getValueD := by
    grind [Data.LLVM.Int.getValueD_eq]
  simp only [Data.RISCV.srli, Data.RISCV.rev8]
  veir_bv_decide

/-- Interpreter computation fact for `riscv.srli` at the immediate `32`. -/
theorem srli_32_interpretOp' (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Riscv.interpretOp' .srli (RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64)))
        resultTypes #[.reg r] blockOperands mem
      = some (.ok (#[.reg (Data.RISCV.srli (BitVec.ofInt 6 32) r)], mem, none)) := rfl

set_option maxHeartbeats 1000000 in
theorem bswap_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps bswap_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges bswap_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds bswap_local}
    {h₄ : LocalRewritePattern.ReturnValues bswap_local} :
    LocalRewritePattern.PreservesSemantics bswap_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, bswap_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchBswap op ctx.raw).isSome := by
    cases hM : matchBswap op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨operand, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Gather the syntactic and verification facts about the matched op.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchBswap_implies hMatch
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by
    rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, hResOperType, intType, isT, hResType⟩ :=
    OperationPtr.Verified.llvm_intr__bswap opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The operand type is the integer type `intType`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [show operand.getType! ctx.raw = ⟨.integerType intType, isT⟩ from by grind]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard fixes `intType.bitwidth ∈ {32, 64}` (the bail branch is the `isTrue` arm).
  peelSplittableCondition [hW] hpattern
  -- Unfold the interpretation of the matched op: exposes the operand's value and its `bswap`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchUnaryOp_interpretOp_unfold (srcOp := .intr__bswap)
      (srcFn := fun x _ => Data.LLVM.Int.bswap x)
      opInBounds hOpType hNumResults hOperands rfl
      (fun _ _ _ _ _ _ => rfl) hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is the byte-swap of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the shared prefix: the `castToRegLocal` and the `rev8` creation.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtx hDom₁
  peelOpCreation! hpattern ctx₂ rev8Op hRev8 hDom₁ hDom₂
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- 64-bit case: `cast → rev8 → castBack`.
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the three created ops.
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRev8Type : rev8Op.getOpType! ctx₃.raw = .riscv .rev8 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRev8Operands : rev8Op.getOperands! ctx₃.raw
        = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (rev8Op.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRev8
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRev8 (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRev8ResTypes : rev8Op.getResultTypes! ctx₃.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rev8Op),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRev8 (operation := rev8Op)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, isT⟩] := by grind
    -- Interpretation tail: `castToReg → rev8 → castBack`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := Data.RISCV.rev8) (fun _ _ _ _ => rfl) hRev8Type hRev8Operands hRev8ResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (Data.RISCV.rev8 (LLVM.Int.toReg xt)) 64)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bswap_isRefinedBy_toInt_rev8 hxtRef⟩
  · -- 32-bit case: `cast → rev8 → srli 32 → castBack`.
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation! hpattern ctx₃ srliOp hSrli hDom₂ hDom₃
    peelReplaceWithRegLocal hpattern ctx₄ castBackOp hCastBack hDom₃ hDom₄
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₄ vNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    -- Structural facts about the four created ops.
    have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
    have hRev8Type : rev8Op.getOpType! ctx₄.raw = .riscv .rev8 := by grind
    have hSrliType : srliOp.getOpType! ctx₄.raw = .riscv .srli := by grind
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₄.raw = #[operand] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRev8 (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hSrli (operation := castOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRev8Operands : rev8Op.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRev8 (operation := rev8Op),
        OperationPtr.getOperands!_WfRewriter_createOp hSrli (operation := rev8Op),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rev8Op)]
    have hSrliOperands : srliOp.getOperands! ctx₄.raw
        = #[ValuePtr.opResult (rev8Op.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hSrli (operation := srliOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := srliOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (srliOp.getResult 0)] := by grind
    have hSrliProps : srliOp.getProperties! ctx₄.raw (.riscv .srli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSrli (operation := srliOp)]
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hSrli
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRev8
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCast
            (value := ValuePtr.opResult (op.getResult 0))]
      simpa only [ValuePtr.getType!_opResult, hResType] using h1
    have hCastResTypes : castOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRev8 (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSrli (operation := castOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
    have hRev8ResTypes : rev8Op.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRev8 (operation := rev8Op),
        OperationPtr.getResultTypes!_WfRewriter_createOp hSrli (operation := rev8Op),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := rev8Op)]
    have hSrliResTypes : srliOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hSrli (operation := srliOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := srliOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, isT⟩] := by grind
    -- Interpretation tail: `castToReg → rev8 → srli 32 → castBack`.
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := Data.RISCV.rev8) (fun _ _ _ _ => rfl) hRev8Type hRev8Operands hRev8ResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := by grind)
        (res := Data.RISCV.srli (BitVec.ofInt 6 32) (Data.RISCV.rev8 (LLVM.Int.toReg xt)))
        (fun rt bo mem => srli_32_interpretOp' _ rt bo mem)
        hSrliType hSrliProps hSrliOperands hSrliResTypes hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32
          (RISCV.Reg.toInt (Data.RISCV.srli (BitVec.ofInt 6 32)
            (Data.RISCV.rev8 (LLVM.Int.toReg xt))) 32)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bswap_isRefinedBy_toInt_srli_rev8 hxtRef⟩

/--
info: 'Veir.bswap_local_preservesSemantics' depends on axioms: [propext,
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
 bswap_isRefinedBy_toInt_rev8._native.bv_decide.ax_1_10,
 bswap_isRefinedBy_toInt_srli_rev8._native.bv_decide.ax_1_11,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms bswap_local_preservesSemantics

end Veir
