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
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate

namespace Veir

/-- Bridge the normalized `roriw` rotate immediate `((amt % 32) + 32) % 32` to the low 5 bits of the
    full-width constant, so the refinement can abstract `BitVec.ofInt 32 amt`. -/
theorem ofInt_5_rotr_mod (amt : Int) :
    BitVec.ofInt 5 (((amt % 32) + 32) % 32) = BitVec.setWidth 5 (BitVec.ofInt 32 amt) := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]
  omega

/-- Correctness of the `riscv.roriw` lowering of a constant-amount `llvm.fshr a a (const amt)` on
    `i32` (a word rotate-right). -/
theorem roriw_isRefinedBy {a at' : Data.LLVM.Int 32} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshr a a (Data.LLVM.Int.constant 32 amt)
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.roriw (BitVec.ofInt 5 (((amt % 32) + 32) % 32)) (LLVM.Int.toReg at')) 32 := by
  rw [Data.RISCV.roriw, ofInt_5_rotr_mod]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 32 amt = v
  revert h
  veir_bv_decide

/-- Bridge the `roliw` (rotate-left, emitted as `roriw` with negated immediate) rotate amount to the
    negation of the low 5 bits of the constant. -/
theorem ofInt_5_rotl_mod (amt : Int) :
    BitVec.ofInt 5 ((32 - (((amt % 32) + 32) % 32)) % 32)
      = -(BitVec.setWidth 5 (BitVec.ofInt 32 amt)) := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_neg, Nat.reducePow]
  omega

/-- Correctness of the `riscv.roriw` lowering of a constant-amount `llvm.fshl a a (const amt)` on
    `i32` (a word rotate-left, emitted as a rotate-right by the negated amount). -/
theorem roliw_isRefinedBy {a at' : Data.LLVM.Int 32} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshl a a (Data.LLVM.Int.constant 32 amt)
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.roriw (BitVec.ofInt 5 ((32 - (((amt % 32) + 32) % 32)) % 32))
            (LLVM.Int.toReg at')) 32 := by
  rw [Data.RISCV.roriw, ofInt_5_rotl_mod]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 32 amt = v
  revert h
  veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the constant word-rotate lowerings (`roriw`/`roliw`): match a
    funnel shift `fshl`/`fshr a a (const amt)` on `i32`, cast `a`, emit `riscv.roriw` with the
    (possibly negated) normalized amount, and cast back. -/
theorem roriwLike_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr)}
    {immOf : Int → Int}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    (local? : WfIRContext OpCode → OperationPtr →
      Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)))
    (hLocal : ∀ ctx op, local? ctx op = (do
      let some (a, b, amt) := match? op ctx.raw | return (ctx, none)
      if a ≠ b then return (ctx, none)
      let some amtAttr := matchConstantIntVal amt ctx.raw | return (ctx, none)
      let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
      if t.bitwidth ≠ 32 then return (ctx, none)
      let (ctx, valCastOp) ← castToRegLocal ctx a
      let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk]
          #[valCastOp.getResult 0] #[] #[]
          (RISCVImmediateProperties.mk (IntegerAttr.mk (immOf amtAttr.value) (IntegerType.mk 64))) none
      let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
      some (ctx, some (#[valCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))))
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {a b amt},
        match? op ctx = some (a, b, amt) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[a, b, amt])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerTernop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y, .int bw z] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y z)], mem, none)))
    (hRefine : ∀ (a at' : Data.LLVM.Int 32) (c : Int), a ⊒ at' →
        srcFn a a (Data.LLVM.Int.constant 32 c)
          ⊒ RISCV.Reg.toInt (Data.RISCV.roriw (BitVec.ofInt 5 (immOf c)) (LLVM.Int.toReg at')) 32)
    {h : LocalRewritePattern.ReturnOps local?}
    {h₂ : LocalRewritePattern.ReturnCtxChanges local?}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds local?}
    {h₄ : LocalRewritePattern.ReturnValues local?} :
    LocalRewritePattern.PreservesSemantics local? h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rw [hLocal] at hpattern
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    hVerified opVerif hOpType
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
    rw [← hOperand0]; rw [hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1]; rw [hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2]; rw [hOp2Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  -- Guard `a = b`.
  have hAeqB : a = b := by
    rcases Decidable.em (a = b) with heq | hne
    · exact heq
    · rw [if_neg hne] at hpattern; simp at hpattern
  rw [if_pos hAeqB] at hpattern
  -- Pin the constant amount.
  have hCstSome : (matchConstantIntVal amt ctx.raw).isSome := by
    cases hM : matchConstantIntVal amt ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨amtAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Width guard `intType.bitwidth = 32`.
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hW32
  obtain ⟨bw⟩ := intType; simp only at hW32 hResType hOp0Type hAType hBType hAmtType; subst bw
  -- Unfold the ternary interpretation.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hSemSrc
      hinterp hAType hBType hAmtType
  subst hCf
  have hxab : xa = xb := by
    have := haVal; rw [hAeqB] at this; rw [hbVal] at this; grind
  subst hxab
  have hDomA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Pin `amt`'s value to the constant.
  have hcConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hAmtType
  obtain rfl : xc = Data.LLVM.Int.constant 32 amtAttr.value := by
    have := hcVal.symm.trans hcConstVal; simpa using this
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the three creations (cast `a`, `roriw`, cast back).
  peelCastToRegLocal hpattern ctx₁ valCastOp hVCast hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ roriwOp hRoriw hDomA₁ hDomA₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDomA₂ hDomA₃
  cleanupHpattern hpattern
  obtain ⟨at', hAVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
      hDomA hDomA₃ aNotOp
  have hVCastType : valCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hRoriwType : roriwOp.getOpType! ctx₃.raw = .riscv .roriw := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hVCastOperands : valCastOp.getOperands! ctx₃.raw = #[a] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hVCast (operation := valCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hRoriw (operation := valCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := valCastOp)]
  have hRoriwOperands : roriwOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (valCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hRoriw (operation := roriwOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := roriwOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (roriwOp.getResult 0)] := by grind
  have hRoriwProps : roriwOp.getProperties! ctx₃.raw (.riscv .roriw)
      = RISCVImmediateProperties.mk (IntegerAttr.mk (immOf amtAttr.value) (IntegerType.mk 64)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hRoriw (operation := roriwOp)]
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hRoriw
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hVCast
          (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact hResType
  have hVCastResTypes : valCastOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hVCast (operation := valCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hRoriw (operation := valCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := valCastOp)]
  have hRoriwResTypes : roriwOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRoriw (operation := roriwOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := roriwOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 32 }, by grind⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hVCastType hVCastOperands hVCastResTypes hAVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := Data.RISCV.roriw (BitVec.ofInt 5 (immOf amtAttr.value)) (LLVM.Int.toReg at'))
      (fun rt bo mem => rfl)
      hRoriwType hRoriwProps hRoriwOperands hRoriwResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 32
        (RISCV.Reg.toInt (Data.RISCV.roriw (BitVec.ofInt 5 (immOf amtAttr.value))
          (LLVM.Int.toReg at')) 32)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hRefine xa at' amtAttr.value haRef⟩

theorem roriw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps roriw_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges roriw_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds roriw_local}
    {h₄ : LocalRewritePattern.ReturnValues roriw_local} :
    LocalRewritePattern.PreservesSemantics roriw_local h h₂ h₃ h₄ :=
  roriwLike_preservesSemantics (srcOp := .intr__fshr)
    (srcFn := fun x y z => Data.LLVM.Int.fshr x y z)
    (immOf := fun c => ((c % 32) + 32) % 32)
    roriw_local (fun _ _ => rfl)
    matchFshr_implies OperationPtr.Verified.llvm_intr__fshr
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a at' c ha => roriw_isRefinedBy c ha)

theorem roliw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps roliw_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges roliw_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds roliw_local}
    {h₄ : LocalRewritePattern.ReturnValues roliw_local} :
    LocalRewritePattern.PreservesSemantics roliw_local h h₂ h₃ h₄ :=
  roriwLike_preservesSemantics (srcOp := .intr__fshl)
    (srcFn := fun x y z => Data.LLVM.Int.fshl x y z)
    (immOf := fun c => (32 - (((c % 32) + 32) % 32)) % 32)
    roliw_local (fun _ _ => rfl)
    matchFshl_implies OperationPtr.Verified.llvm_intr__fshl
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a at' c ha => roliw_isRefinedBy c ha)

/--
info: 'Veir.roriw_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 roriw_isRefinedBy._native.bv_decide.ax_1_7,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms roriw_local_preservesSemantics

/--
info: 'Veir.roliw_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 roliw_isRefinedBy._native.bv_decide.ax_1_7,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms roliw_local_preservesSemantics

end Veir
