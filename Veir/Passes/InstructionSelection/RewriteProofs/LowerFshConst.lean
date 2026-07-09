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
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate

namespace Veir

/-!
## Correctness of the GlobalISel constant word-rotate lowerings (`fshrConst`/`fshlConst`)

`llvm.fshr a a (const)` and `llvm.fshl a a (const)` on `i64`/`i32` are constant rotates, lowered to
`riscv.rori` (i64) or `riscv.roriw` (i32) with the normalized 5-bit or 6-bit amount (negated for
`fshl`, which has no rotate-left instruction).
-/

/-! ### Immediate bridges: normalized rotate amount ↔ low bits of the constant. -/

theorem ofInt_6_rotr (amt : Int) :
    BitVec.ofInt 6 (((amt % 64) + 64) % 64) = BitVec.setWidth 6 (BitVec.ofInt 64 amt) := by
  rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega

theorem ofInt_6_rotl (amt : Int) :
    BitVec.ofInt 6 ((64 - (((amt % 64) + 64) % 64)) % 64) = -(BitVec.setWidth 6 (BitVec.ofInt 64 amt)) := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_neg, Nat.reducePow]; omega

theorem ofInt_5_rotr (amt : Int) :
    BitVec.ofInt 5 (((amt % 32) + 32) % 32) = BitVec.setWidth 5 (BitVec.ofInt 32 amt) := by
  rw [← BitVec.toNat_inj]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]; omega

theorem ofInt_5_rotl (amt : Int) :
    BitVec.ofInt 5 ((32 - (((amt % 32) + 32) % 32)) % 32) = -(BitVec.setWidth 5 (BitVec.ofInt 32 amt)) := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_neg, Nat.reducePow]; omega

/-! ### Rotate refinement data lemmas. -/

theorem fshr_rori_64 {a at' : Data.LLVM.Int 64} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshr a a (Data.LLVM.Int.constant 64 amt)
      ⊒ RISCV.Reg.toInt (Data.RISCV.rori (BitVec.ofInt 6 (((amt % 64) + 64) % 64)) (LLVM.Int.toReg at')) 64 := by
  rw [Data.RISCV.rori, ofInt_6_rotr]; simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 amt = v; revert h; veir_bv_decide

theorem fshl_rori_64 {a at' : Data.LLVM.Int 64} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshl a a (Data.LLVM.Int.constant 64 amt)
      ⊒ RISCV.Reg.toInt (Data.RISCV.rori (BitVec.ofInt 6 ((64 - (((amt % 64) + 64) % 64)) % 64)) (LLVM.Int.toReg at')) 64 := by
  rw [Data.RISCV.rori, ofInt_6_rotl]; simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 amt = v; revert h; veir_bv_decide

theorem fshr_roriw_32 {a at' : Data.LLVM.Int 32} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshr a a (Data.LLVM.Int.constant 32 amt)
      ⊒ RISCV.Reg.toInt (Data.RISCV.roriw (BitVec.ofInt 5 (((amt % 32) + 32) % 32)) (LLVM.Int.toReg at')) 32 := by
  rw [Data.RISCV.roriw, ofInt_5_rotr]; simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 32 amt = v; revert h; veir_bv_decide

theorem fshl_roriw_32 {a at' : Data.LLVM.Int 32} (amt : Int) (h : a ⊒ at') :
    Data.LLVM.Int.fshl a a (Data.LLVM.Int.constant 32 amt)
      ⊒ RISCV.Reg.toInt (Data.RISCV.roriw (BitVec.ofInt 5 ((32 - (((amt % 32) + 32) % 32)) % 32)) (LLVM.Int.toReg at')) 32 := by
  rw [Data.RISCV.roriw, ofInt_5_rotl]; simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 32 amt = v; revert h; veir_bv_decide

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the GlobalISel constant word-rotate lowerings (`fshrConst`/
    `fshlConst`): match `fshl`/`fshr a a (const amt)` on `i64`/`i32`, cast `a`, then (bitwidth
    branch) emit `riscv.rori` (i64) or `riscv.roriw` (i32) with the appropriate immediate, and cast
    back. -/
theorem fshConstLike_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr)}
    {imm32 imm64 : Int → Int} {r32 r64 : Int → Data.RISCV.Reg → Data.RISCV.Reg}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    (local? : WfIRContext OpCode → OperationPtr →
      Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)))
    (hLocal : ∀ ctx op, local? ctx op = (do
      let some (a, b, amt) := match? op ctx.raw | return (ctx, none)
      if a ≠ b then return (ctx, none)
      let some amtAttr := matchConstantIntVal amt ctx.raw | return (ctx, none)
      let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
      if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
      let (ctx, valCastOp) ← castToRegLocal ctx a
      if t.bitwidth = 32 then
        let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk]
            #[valCastOp.getResult 0] #[] #[]
            (RISCVImmediateProperties.mk (IntegerAttr.mk (imm32 amtAttr.value) (IntegerType.mk 64))) none
        let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
        some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))
      else
        let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .rori) #[RegisterType.mk]
            #[valCastOp.getResult 0] #[] #[]
            (RISCVImmediateProperties.mk (IntegerAttr.mk (imm64 amtAttr.value) (IntegerType.mk 64))) none
        let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
        some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))))
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {a b amt},
        match? op ctx = some (a, b, amt) →
        op.getOpType! ctx = .llvm srcOp ∧ op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[a, b, amt])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr} {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedIntegerTernop ctx)
    (hSemSrc : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y, .int bw z] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y z)], mem, none)))
    (hSemR32 : ∀ (c : Int) (r : Data.RISCV.Reg) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Riscv.interpretOp' .roriw (RISCVImmediateProperties.mk (IntegerAttr.mk c (IntegerType.mk 64)))
          rt #[.reg r] bo mem = some (.ok (#[.reg (r32 c r)], mem, none)))
    (hSemR64 : ∀ (c : Int) (r : Data.RISCV.Reg) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Riscv.interpretOp' .rori (RISCVImmediateProperties.mk (IntegerAttr.mk c (IntegerType.mk 64)))
          rt #[.reg r] bo mem = some (.ok (#[.reg (r64 c r)], mem, none)))
    (hRefine32 : ∀ (a at' : Data.LLVM.Int 32) (c : Int), a ⊒ at' →
        srcFn a a (Data.LLVM.Int.constant 32 c) ⊒ RISCV.Reg.toInt (r32 (imm32 c) (LLVM.Int.toReg at')) 32)
    (hRefine64 : ∀ (a at' : Data.LLVM.Int 64) (c : Int), a ⊒ at' →
        srcFn a a (Data.LLVM.Int.constant 64 c) ⊒ RISCV.Reg.toInt (r64 (imm64 c) (LLVM.Int.toReg at')) 64)
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
  have hAeqB : a = b := by
    rcases Decidable.em (a = b) with heq | hne
    · exact heq
    · rw [if_neg hne] at hpattern; simp at hpattern
  rw [if_pos hAeqB] at hpattern
  have hCstSome : (matchConstantIntVal amt ctx.raw).isSome := by
    cases hM : matchConstantIntVal amt ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨amtAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  -- Width guard `intType.bitwidth ∈ {64, 32}`.
  split at hpattern
  case isTrue hne => simp at hpattern
  rename_i hWidthRaw
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hSemSrc
      hinterp hAType hBType hAmtType
  subst hCf
  have hxab : xa = xb := by
    have := haVal; rw [hAeqB] at this; rw [hbVal] at this; grind
  subst hxab
  have hDomA : a.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hcConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hAmtType
  obtain rfl : xc = Data.LLVM.Int.constant intType.bitwidth amtAttr.value := by
    have := hcVal.symm.trans hcConstVal; simpa using this
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have aNotOp : ¬ a ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the shared cast of `a`, then branch on the bitwidth.
  peelCastToRegLocal hpattern ctx₁ valCastOp hVCast hDomA hDomA₁
  have hBwCases : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  rcases hBwCases with hbw | hbw
  · -- `i64`: emit `riscv.rori`.
    rw [if_neg (show ¬intType.bitwidth = 32 by omega)] at hpattern
    peelOpCreation! hpattern ctx₂ roriOp hRori hDomA₁ hDomA₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDomA₂ hDomA₃
    cleanupHpattern hpattern
    obtain ⟨at', hAVal', haRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomA hDomA₃ aNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw haVal hRes hResType ⊢; subst bw
    have hVCastType : valCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRoriType : roriOp.getOpType! ctx₃.raw = .riscv .rori := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hVCastOperands : valCastOp.getOperands! ctx₃.raw = #[a] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hVCast (operation := valCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRori (operation := valCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := valCastOp)]
    have hRoriOperands : roriOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (valCastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (roriOp.getResult 0)] := by grind
    have hRoriProps : roriOp.getProperties! ctx₃.raw (.riscv .rori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (imm64 amtAttr.value) (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hRori (operation := roriOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRori (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hVCast (value := ValuePtr.opResult (op.getResult 0))]
      rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
      rw [h1]; exact hResType
    have hVCastResTypes : valCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hVCast (operation := valCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := valCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := valCastOp)]
    have hRoriResTypes : roriOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hVCastType hVCastOperands hVCastResTypes hAVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := r64 (imm64 amtAttr.value) (LLVM.Int.toReg at'))
        (fun rt bo mem => hSemR64 (imm64 amtAttr.value) _ rt bo mem)
        hRoriType hRoriProps hRoriOperands hRoriResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 64
          (RISCV.Reg.toInt (r64 (imm64 amtAttr.value) (LLVM.Int.toReg at')) 64)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine64 xa at' amtAttr.value haRef⟩
  · -- `i32`: emit `riscv.roriw`.
    rw [if_pos (show intType.bitwidth = 32 by omega)] at hpattern
    peelOpCreation! hpattern ctx₂ roriOp hRori hDomA₁ hDomA₂
    peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hDomA₂ hDomA₃
    cleanupHpattern hpattern
    obtain ⟨at', hAVal', haRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) haVal
        hDomA hDomA₃ aNotOp
    obtain ⟨bw⟩ := intType; simp only at hbw haVal hRes hResType ⊢; subst bw
    have hVCastType : valCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hRoriType : roriOp.getOpType! ctx₃.raw = .riscv .roriw := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
      grind
    have hVCastOperands : valCastOp.getOperands! ctx₃.raw = #[a] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hVCast (operation := valCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hRori (operation := valCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := valCastOp)]
    have hRoriOperands : roriOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (valCastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (roriOp.getResult 0)] := by grind
    have hRoriProps : roriOp.getProperties! ctx₃.raw (.riscv .roriw)
        = RISCVImmediateProperties.mk (IntegerAttr.mk (imm32 amtAttr.value) (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hRori (operation := roriOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType { bitwidth := 32 }, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hRori (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hVCast (value := ValuePtr.opResult (op.getResult 0))]
      rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
      rw [h1]; exact hResType
    have hVCastResTypes : valCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hVCast (operation := valCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := valCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := valCastOp)]
    have hRoriResTypes : roriOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hRori (operation := roriOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := roriOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType { bitwidth := 32 }, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hVCastType hVCastOperands hVCastResTypes hAVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := r32 (imm32 amtAttr.value) (LLVM.Int.toReg at'))
        (fun rt bo mem => hSemR32 (imm32 amtAttr.value) _ rt bo mem)
        hRoriType hRoriProps hRoriOperands hRoriResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 32
          (RISCV.Reg.toInt (r32 (imm32 amtAttr.value) (LLVM.Int.toReg at')) 32)], ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
          ⟨rfl, by simpa using hRefine32 xa at' amtAttr.value haRef⟩

theorem fshrConst_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps fshrConst_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges fshrConst_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds fshrConst_local}
    {h₄ : LocalRewritePattern.ReturnValues fshrConst_local} :
    LocalRewritePattern.PreservesSemantics fshrConst_local h h₂ h₃ h₄ :=
  fshConstLike_preservesSemantics (srcOp := .intr__fshr)
    (srcFn := fun x y z => Data.LLVM.Int.fshr x y z)
    (imm32 := fun c => ((c % 32) + 32) % 32) (imm64 := fun c => ((c % 64) + 64) % 64)
    (r32 := fun x r => Data.RISCV.roriw (BitVec.ofInt 5 x) r)
    (r64 := fun x r => Data.RISCV.rori (BitVec.ofInt 6 x) r)
    fshrConst_local (fun _ _ => rfl)
    matchFshr_implies OperationPtr.Verified.llvm_intr__fshr
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ c ha => fshr_roriw_32 c ha) (fun _ _ c ha => fshr_rori_64 c ha)

theorem fshlConst_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps fshlConst_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges fshlConst_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds fshlConst_local}
    {h₄ : LocalRewritePattern.ReturnValues fshlConst_local} :
    LocalRewritePattern.PreservesSemantics fshlConst_local h h₂ h₃ h₄ :=
  fshConstLike_preservesSemantics (srcOp := .intr__fshl)
    (srcFn := fun x y z => Data.LLVM.Int.fshl x y z)
    (imm32 := fun c => (32 - (((c % 32) + 32) % 32)) % 32)
    (imm64 := fun c => (64 - (((c % 64) + 64) % 64)) % 64)
    (r32 := fun x r => Data.RISCV.roriw (BitVec.ofInt 5 x) r)
    (r64 := fun x r => Data.RISCV.rori (BitVec.ofInt 6 x) r)
    fshlConst_local (fun _ _ => rfl)
    matchFshl_implies OperationPtr.Verified.llvm_intr__fshl
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ c ha => fshl_roriw_32 c ha) (fun _ _ c ha => fshl_rori_64 c ha)

/--
info: 'Veir.fshrConst_local_preservesSemantics' depends on axioms: [propext,
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
 fshr_rori_64._native.bv_decide.ax_1_7,
 fshr_roriw_32._native.bv_decide.ax_1_7,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms fshrConst_local_preservesSemantics

/--
info: 'Veir.fshlConst_local_preservesSemantics' depends on axioms: [propext,
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
 fshl_rori_64._native.bv_decide.ax_1_7,
 fshl_roriw_32._native.bv_decide.ax_1_7,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms fshlConst_local_preservesSemantics

end Veir
