import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW

namespace Veir

/-!
## Correctness of `bswap_local`

`llvm.intr.bswap` on a 64- or 32-bit integer is lowered to
`unrealized_conversion_cast` (to a register) → `riscv.rev8`, and for `i32` an extra `riscv.srli 32`
(because `rev8` reverses all 8 bytes, so an `i32`'s meaningful bytes land in the high 32 bits and
must be shifted back down) → `unrealized_conversion_cast` (back to the integer type).

`bswap` does not fit `lowerUnaryWLocal`: its `i32` branch emits *two* register ops (`rev8` then the
immediate `srli 32`) rather than a single `W`-variant, so it is proven bespoke. The `i64` branch is
structurally identical to a `lowerUnaryWLocal` `i64` branch (`castToReg → rev8 → castBack`); the
`i32` branch threads one extra `interpretOp_riscv_srli_forward` step (the immediate analogue of the
plain unary-register forward lemma) between `rev8` and the cast-back.
-/

/-- Forward-interpretation lemma for the immediate `riscv.srli`. Unlike
    `interpretOp_riscv_unaryReg_forward`, the emitted register is a function of the op's *shift
    immediate*, read from its properties, so the caller supplies that immediate as `k` together with
    the reduction `hImm` of the op's stored property value. Interpreting the op succeeds, leaves
    memory untouched, binds the result to `.reg (Data.RISCV.srli k r)`, and leaves every non-result
    value unchanged. -/
theorem interpretOp_riscv_srli_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {v : ValuePtr} {rt : RegisterType} {hIsTy}
    {r : Data.RISCV.Reg} {k : BitVec 6}
    (hType : theOp.getOpType! ctx.raw = .riscv .srli)
    (hImm : BitVec.ofInt 6 (theOp.getProperties! ctx.raw (.riscv .srli)).value.value = k)
    (hOperands : theOp.getOperands! ctx.raw = #[v])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩])
    (hVal : state.variables.getVar? v = some (.reg r)) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.srli k r)) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[.reg r]) (results := #[.reg (Data.RISCV.srli k r)]) (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands, hVal])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp [interpretOp', Riscv.interpretOp', Interp, hImm, pure])
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  grind

/-- Correctness of the `riscv.rev8` lowering of a 64-bit `llvm.intr.bswap`: the round trip
    `int → reg → rev8 → int` refines `bswap`. (`xt` is the possibly-more-defined target-side value
    of the operand.) -/
theorem bswap_isRefinedBy_toInt_rev8 {x xt : Data.LLVM.Int 64} (h : x ⊒ xt) :
    Data.LLVM.Int.bswap x ⊒ RISCV.Reg.toInt (Data.RISCV.rev8 (LLVM.Int.toReg xt)) 64 := by
  revert h
  veir_bv_decide

/-- Correctness of the `riscv.srli 32 (rev8 ·)` lowering of a 32-bit `llvm.intr.bswap`: `rev8`
    reverses all 8 register bytes, so the reversed `i32` lands in the high word; `srli 32` shifts it
    back down before the truncating cast reads the low 32 bits. -/
theorem bswap_isRefinedBy_toInt_srli_rev8 {x xt : Data.LLVM.Int 32} (h : x ⊒ xt) :
    Data.LLVM.Int.bswap x ⊒
      RISCV.Reg.toInt (Data.RISCV.srli (BitVec.ofInt 6 32) (Data.RISCV.rev8 (LLVM.Int.toReg xt)))
        32 := by
  revert h
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Correctness of the `bswap_local` lowering: the `castToReg → rev8 (→ srli 32 for i32) → castBack`
    round trip refines `llvm.intr.bswap`. -/
theorem bswap_local_preservesSemantics :
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
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, hResOperType, intType, isT, hResType⟩ :=
    OperationPtr.Verified.llvm_intr__bswap opVerif hOpType
  -- The operand type is the integer type `intType`; resolve the type-destructuring match.
  have hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [show operand.getType! ctx.raw = ⟨.integerType intType, isT⟩ from by grind]
  rw [hOperandType] at hpattern
  simp only [] at hpattern
  -- Unfold the interpretation of the matched op: exposes the operand's value and `bswap`.
  obtain ⟨xVal, hxVal, hMem, hRes, hCf⟩ :=
    matchUnaryOp_interpretOp_unfold (srcFn := fun {_} x _ => Data.LLVM.Int.bswap x)
      opInBounds hOpType hNumResults hOperands rfl (fun _ _ _ _ _ _ => rfl) hinterp hOperandType
  subst hCf
  -- The matched operand dominates the rewrite point in the source context.
  have hDomCtx : operand.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- The bitwidth guard must be false (otherwise the RHS would be `some (ctx, none)`).
  peelSplittableCondition [hBw] hpattern
  -- Source value: `op`'s single result is `bswap` of its operand.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `operand` is not one of `op`'s results.
  have vNotOp : ¬ operand ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the `castToReg` and the `rev8` creations shared by both branches.
  peelCastToRegLocal hpattern ctx₁ castOp hCast hDomCtx hDom₁
  peelOpCreation! hpattern ctx₂ rev8Op hRev8 hDom₁ hDom₂
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- 64-bit case: `castToReg → rev8 → castBack`.
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    simp only [] at hpattern
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDom₂ hDom₃
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₃ vNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
    have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRev8Type : rev8Op.getOpType! ctx₃.raw = .riscv .rev8 := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hCastOperands : castOp.getOperands! ctx₃.raw = #[operand] := by grind
    have hRev8Operands :
        rev8Op.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (rev8Op.getResult 0)] := by grind
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRev8
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp]
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
    · refine ⟨#[RuntimeValue.int 64 (RISCV.Reg.toInt (Data.RISCV.rev8 (LLVM.Int.toReg xt)) 64)],
        ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bswap_isRefinedBy_toInt_rev8 hxtRef⟩
  · -- 32-bit case: `castToReg → rev8 → srli 32 → castBack`.
    rw [if_pos hbw] at hpattern
    simp only [] at hpattern
    peelOpCreation! hpattern ctx₃ srliOp hSrli hDom₂ hDom₃
    peelReplaceWithRegLocal hpattern ctx₄ castBackOp hCastBack hDom₃ hDom₄
    cleanupHpattern hpattern
    obtain ⟨xt, hOpVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
        hDomCtx hDom₄ vNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw; subst hbw
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
    have hRev8Operands :
        rev8Op.getOperands! ctx₄.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRev8 (operation := rev8Op),
        OperationPtr.getOperands!_WfRewriter_createOp hSrli (operation := rev8Op),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := rev8Op)]
    have hSrliOperands :
        srliOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (rev8Op.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hSrli (operation := srliOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := srliOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (srliOp.getResult 0)] := by grind
    have hSrliProps : srliOp.getProperties! ctx₄.raw (.riscv .srli)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hSrli (operation := srliOp)]
    have hSrliImm : BitVec.ofInt 6 (srliOp.getProperties! ctx₄.raw (.riscv .srli)).value.value
        = BitVec.ofInt 6 32 := by rw [hSrliProps]
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, isT⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hSrli
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hRev8
            (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp]
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
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastType hCastOperands hCastResTypes hOpVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
        (f := Data.RISCV.rev8) (fun _ _ _ _ => rfl) hRev8Type hRev8Operands hRev8ResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_riscv_srli_forward (state := s₂) (inBounds := by grind)
        (k := BitVec.ofInt 6 32) hSrliType hSrliImm hSrliOperands hSrliResTypes hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32 (RISCV.Reg.toInt
          (Data.RISCV.srli (BitVec.ofInt 6 32) (Data.RISCV.rev8 (LLVM.Int.toReg xt))) 32)], ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using bswap_isRefinedBy_toInt_srli_rev8 hxtRef⟩

end Veir
