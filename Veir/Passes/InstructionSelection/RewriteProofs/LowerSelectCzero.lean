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

namespace Veir

/-!
## Correctness of the branchless `llvm.select` lowerings (`selectCzeroeqz`/`selectCzeronez`)

`llvm.select c t 0` lowers to `riscv.czeroeqz t c` (which is `c = 0 ? 0 : t`), and `llvm.select c 0 f`
to `riscv.czeronez f c` (`c ≠ 0 ? 0 : f`). Both cast the (non-zero) value operand and the `i1`
condition to registers, emit the `czero` op, and cast the result back; the constant-zero operand is
folded away (matched with `matchConstantZero`, whose value is pinned via the constant graph lemma).
-/

/-- `select`-specialised interpretation unfold: the condition (operand 0) has type `i1` while the two
    value operands share type `intType`, so `matchTernaryOp_interpretOp_unfold` (all-same-width) does
    not apply. Exposes the three operand values and the `LLVM.Int.select` result. -/
theorem matchSelectOp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {cond tval fval : ValuePtr} {intType}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .select)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[cond, tval, fval])
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩)
    (hTValType : (tval.getType! ctx.raw).val = Attribute.integerType intType)
    (hFValType : (fval.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ (c : Data.LLVM.Int 1) (t f : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? cond = some (RuntimeValue.int 1 c) ∧
      state.variables.getVar? tval = some (RuntimeValue.int intType.bitwidth t) ∧
      state.variables.getVar? fval = some (RuntimeValue.int intType.bitwidth f) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (Data.LLVM.Int.select c t f)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 3 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTValEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFValEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize2 : 2 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨cval, hcval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨tval', htval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  obtain ⟨fval', hfval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 2 hsize2
  have hcGetVar : state.variables.getVar? cond = some cval := by
    rw [hCondEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hcval
  have htGetVar : state.variables.getVar? tval = some tval' := by
    rw [hTValEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact htval
  have hfGetVar : state.variables.getVar? fval = some fval' := by
    rw [hFValEq, show (op.getOperands! ctx.raw)[2]! = (op.getOperands! ctx.raw)[2] from by grind]
    exact hfval
  have hcconf := VariableState.getVar?_conforms hcGetVar
  rw [show cond.getType! ctx.raw = ⟨.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩
        from Subtype.ext hCondType] at hcconf
  obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType hcconf
  have htconf := VariableState.getVar?_conforms htGetVar
  rw [show tval.getType! ctx.raw = ⟨.integerType intType, hTValType ▸ (tval.getType! ctx.raw).2⟩
        from Subtype.ext hTValType] at htconf
  obtain ⟨t, rfl⟩ := RuntimeValue.Conforms.integerType htconf
  have hfconf := VariableState.getVar?_conforms hfGetVar
  rw [show fval.getType! ctx.raw = ⟨.integerType intType, hFValType ▸ (fval.getType! ctx.raw).2⟩
        from Subtype.ext hFValType] at hfconf
  obtain ⟨f, rfl⟩ := RuntimeValue.Conforms.integerType hfconf
  refine ⟨c, t, f, hcGetVar, htGetVar, hfGetVar, ?_⟩
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int 1 c, RuntimeValue.int intType.bitwidth t,
          RuntimeValue.int intType.bitwidth f] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa [hOperand0] using hcGetVar
    · simpa [hOperand1] using htGetVar
    · simpa [hOperand2] using hfGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int intType.bitwidth (Data.LLVM.Int.select c t f)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Correctness of `riscv.czeroeqz` for `llvm.select c t 0` (widths `{32, 64}`): the round trip
    refines `select`. -/
theorem czeroeqz_isRefinedBy {width : Nat} {c ct : Data.LLVM.Int 1} {t tt : Data.LLVM.Int width}
    (hw : width = 64 ∨ width = 32) (hc : c ⊒ ct) (ht : t ⊒ tt) :
    Data.LLVM.Int.select c t (Data.LLVM.Int.constant width 0)
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt)) width := by
  rcases hw with rfl | rfl <;> (revert hc ht; veir_bv_decide)

/-- Correctness of `riscv.czeronez` for `llvm.select c 0 f` (widths `{32, 64}`). -/
theorem czeronez_isRefinedBy {width : Nat} {c ct : Data.LLVM.Int 1} {f ft : Data.LLVM.Int width}
    (hw : width = 64 ∨ width = 32) (hc : c ⊒ ct) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c (Data.LLVM.Int.constant width 0) f
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft)) width := by
  rcases hw with rfl | rfl <;> (revert hc hf; veir_bv_decide)

set_option maxHeartbeats 1000000 in
theorem selectCzeroeqz_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps selectCzeroeqz_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges selectCzeroeqz_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds selectCzeroeqz_local}
    {h₄ : LocalRewritePattern.ReturnValues selectCzeroeqz_local} :
    LocalRewritePattern.PreservesSemantics selectCzeroeqz_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectCzeroeqz_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the `matchSelect`.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, ⟨condIt, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTValEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFValEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be integer for the pattern to fire.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTValType : (tval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFValType : (fval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Width guard: `intType.bitwidth ∈ {64, 32}`.
  split at hpattern
  case isTrue hne => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  -- The dropped operand `fval` is a constant zero.
  have hCstSome : (matchConstantZero fval ctx.raw).isSome := by
    cases hM : matchConstantZero fval ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨fzero, hCzMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCzMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨-, imm, hCstMatch, hImmZero⟩ := matchConstantZero_implies hCzMatch
  -- Unfold the select interpretation.
  obtain ⟨cv, tv, fv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hinterp
      hCondType hTValType hFValType
  subst hCf
  -- Pin `fval`'s value to the constant zero.
  have hfConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hFValType
  obtain rfl : fv = Data.LLVM.Int.constant intType.bitwidth imm.value := by
    have := hfVal.symm.trans hfConstVal; simpa using this
  rw [hImmZero] at hRes
  -- The two matched operands `tval`/`cond` dominate the rewrite point.
  have hDomT : tval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s result is `select c t 0`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have tNotOp : ¬ tval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the four op creations, transporting both `tval` and `cond` dominance.
  peelCastToRegLocal₂ hpattern ctx₁ tCastOp hTCast hDomT hDomT₁ hDomC hDomC₁
  peelCastToRegLocal₂ hpattern ctx₂ condCastOp hCondCast hDomT₁ hDomT₂ hDomC₁ hDomC₂
  peelOpCreation!₂ hpattern ctx₃ czOp hCz hDomT₂ hDomT₃ hDomC₂ hDomC₃
  peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomT₃ hDomT₄ hDomC₃ hDomC₄
  cleanupHpattern hpattern
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) htVal
      hDomT hDomT₄ tNotOp
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
      hDomC hDomC₄ cNotOp
  -- Freshness facts for the frame clauses.
  have hTCastFresh : ¬ tCastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds tCastOp hTCast
  have hCondIn : cond.InBounds ctx.raw := by grind
  have hCondNeTCastRes : ∀ i, cond ≠ ValuePtr.opResult (tCastOp.getResult i) := by
    intro i heq
    rw [heq] at hCondIn
    rw [ValuePtr.inBounds_opResult] at hCondIn
    obtain ⟨hIn, -⟩ := hCondIn
    exact hTCastFresh hIn
  have hTCastNeCondCast : tCastOp ≠ condCastOp := by grind
  -- Structural facts about the four created ops.
  have hTCastType : tCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCondCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCondCastType : condCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzType : czOp.getOpType! ctx₄.raw = .riscv .czeroeqz := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := castBackOp)]
  have hTCastOperands : tCastOp.getOperands! ctx₄.raw = #[tval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCondCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCondCastOperands : condCastOp.getOperands! ctx₄.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzOperands : czOp.getOperands! ctx₄.raw
      = #[ValuePtr.opResult (tCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (czOp.getResult 0)] := by grind
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType intType, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hCz
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCondCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hTCast
          (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact Subtype.ext hResType
  have hTCastResTypes : tCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCondCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCondCastResTypes : condCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzResTypes : czOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType intType, by grind⟩] := by grind
  -- Interpretation tail.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hTCastType hTCastOperands hTCastResTypes hTVal'
  have hCondNotTCastRes : cond ∉ tCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw cond tCastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hCondNeTCastRes i)
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond hCondNotTCastRes]; exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hCondCastType hCondCastOperands hCondCastResTypes hCVal₁
  have hRes₁' : s₂.variables.getVar? (ValuePtr.opResult (tCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg tt)) := by
    rw [hFrame₂ _ (by
      apply ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds (ctx := ctx₁.raw)
        (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
          OperationPtr.getNumResults!_WfRewriter_createOp hTCast (operation := tCastOp)])
        (by grind))]
    exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl)
      hCzType hCzOperands hCzResTypes hRes₁' hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int intType.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))
          intType.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using czeroeqz_isRefinedBy (by omega) hcRef htRef⟩


set_option maxHeartbeats 1000000 in
theorem selectCzeronez_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps selectCzeronez_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges selectCzeronez_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds selectCzeronez_local}
    {h₄ : LocalRewritePattern.ReturnValues selectCzeronez_local} :
    LocalRewritePattern.PreservesSemantics selectCzeronez_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectCzeronez_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the `matchSelect`.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, ⟨condIt, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTValEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFValEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be integer for the pattern to fire.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTValType : (tval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFValType : (fval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Width guard: `intType.bitwidth ∈ {64, 32}`.
  split at hpattern
  case isTrue hne => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  -- The dropped operand `tval` is a constant zero.
  have hCstSome : (matchConstantZero tval ctx.raw).isSome := by
    cases hM : matchConstantZero tval ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨fzero, hCzMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCzMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨-, imm, hCstMatch, hImmZero⟩ := matchConstantZero_implies hCzMatch
  -- Unfold the select interpretation.
  obtain ⟨cv, tv, fv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hinterp
      hCondType hTValType hFValType
  subst hCf
  -- Pin `tval`'s value to the constant zero.
  have htConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hTValType
  obtain rfl : tv = Data.LLVM.Int.constant intType.bitwidth imm.value := by
    have := htVal.symm.trans htConstVal; simpa using this
  rw [hImmZero] at hRes
  -- The two matched operands `tval`/`cond` dominate the rewrite point.
  have hDomF : fval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s result is `select c 0 f`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have fNotOp : ¬ fval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the four op creations, transporting both `fval` and `cond` dominance.
  peelCastToRegLocal₂ hpattern ctx₁ fCastOp hFCast hDomF hDomF₁ hDomC hDomC₁
  peelCastToRegLocal₂ hpattern ctx₂ condCastOp hCondCast hDomF₁ hDomF₂ hDomC₁ hDomC₂
  peelOpCreation!₂ hpattern ctx₃ czOp hCz hDomF₂ hDomF₃ hDomC₂ hDomC₃
  peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomF₃ hDomF₄ hDomC₃ hDomC₄
  cleanupHpattern hpattern
  obtain ⟨ft, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hfVal
      hDomF hDomF₄ fNotOp
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
      hDomC hDomC₄ cNotOp
  -- Freshness facts for the frame clauses.
  have hFCastFresh : ¬ fCastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds fCastOp hFCast
  have hCondIn : cond.InBounds ctx.raw := by grind
  have hCondNeFCastRes : ∀ i, cond ≠ ValuePtr.opResult (fCastOp.getResult i) := by
    intro i heq
    rw [heq] at hCondIn
    rw [ValuePtr.inBounds_opResult] at hCondIn
    obtain ⟨hIn, -⟩ := hCondIn
    exact hFCastFresh hIn
  have hFCastNeCondCast : fCastOp ≠ condCastOp := by grind
  -- Structural facts about the four created ops.
  have hFCastType : fCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCondCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCondCastType : condCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzType : czOp.getOpType! ctx₄.raw = .riscv .czeronez := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := castBackOp)]
  have hFCastOperands : fCastOp.getOperands! ctx₄.raw = #[fval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCondCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCondCastOperands : condCastOp.getOperands! ctx₄.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzOperands : czOp.getOperands! ctx₄.raw
      = #[ValuePtr.opResult (fCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (czOp.getResult 0)] := by grind
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType intType, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hCz
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCondCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hFCast
          (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact Subtype.ext hResType
  have hFCastResTypes : fCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCondCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCondCastResTypes : condCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCondCast (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzResTypes : czOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType intType, by grind⟩] := by grind
  -- Interpretation tail.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hFCastType hFCastOperands hFCastResTypes hFVal'
  have hCondNotFCastRes : cond ∉ fCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw cond fCastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hCondNeFCastRes i)
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond hCondNotFCastRes]; exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hCondCastType hCondCastOperands hCondCastResTypes hCVal₁
  have hRes₁' : s₂.variables.getVar? (ValuePtr.opResult (fCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg ft)) := by
    rw [hFrame₂ _ (by
      apply ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds (ctx := ctx₁.raw)
        (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
          OperationPtr.getNumResults!_WfRewriter_createOp hFCast (operation := fCastOp)])
        (by grind))]
    exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl)
      hCzType hCzOperands hCzResTypes hRes₁' hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int intType.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          intType.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using czeronez_isRefinedBy (by omega) hcRef hfRef⟩

/--
info: 'Veir.selectCzeroeqz_local_preservesSemantics' depends on axioms: [propext,
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
 czeroeqz_isRefinedBy._native.bv_decide.ax_1_10,
 czeroeqz_isRefinedBy._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms selectCzeroeqz_local_preservesSemantics

/--
info: 'Veir.selectCzeronez_local_preservesSemantics' depends on axioms: [propext,
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
 czeronez_isRefinedBy._native.bv_decide.ax_1_10,
 czeronez_isRefinedBy._native.bv_decide.ax_1_5,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms selectCzeronez_local_preservesSemantics

end Veir
