import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Refinement
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas

namespace Veir

/-!
## Correctness of `selectCzeroeqz_local`

`llvm.select c t 0` (on `i64`/`i32`, with the false arm matched to a zero constant) is lowered
to the Zicond branchless idiom `czero.eqz t, c`:
`unrealized_conversion_cast` (each of `t` and `c` to a register) → `riscv.czeroeqz` →
`unrealized_conversion_cast` (back to the integer type).

Structurally this is the two-operand cast prefix of `usubSat_local` followed by a single
register op and a cast-back. Two new ingredients over the binary lowerings: the source op is
`select`, whose operands have mixed widths (the condition is `i1`, the values are `i{w}`), handled
by the bespoke `matchSelectOp_interpretOp_unfold`; and the false arm is matched only
*syntactically* as a zero constant, so its runtime value is recovered from the source state's
`EquationLemmaAt` invariant via `matchConstantIntVal_getVar?_of_EquationLemmaAt`.
-/


/-! ### Forward unfolding of a `select` interpretation -/

set_option maxHeartbeats 800000 in
/-- Interpreting a matched `llvm.select` whose condition (operand 0) has an `i1` type and whose
    two value operands (1 and 2) have integer type `valType` reads the operands' values `c`/`tv`/
    `fv` and stores `select c tv fv` in the result variable, leaving memory and control flow
    untouched. The mixed-width analogue of `matchBinaryOp_interpretOp_unfold`. -/
theorem matchSelectOp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {cond tval fval : ValuePtr} {valType : IntegerType}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .select)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[cond, tval, fval])
    (hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩)
    (hTvalType : (tval.getType! ctx.raw).val = Attribute.integerType valType)
    (hFvalType : (fval.getType! ctx.raw).val = Attribute.integerType valType)
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (c : Data.LLVM.Int 1) (tv fv : Data.LLVM.Int valType.bitwidth),
      state.variables.getVar? cond = some (RuntimeValue.int 1 c) ∧
      state.variables.getVar? tval = some (RuntimeValue.int valType.bitwidth tv) ∧
      state.variables.getVar? fval = some (RuntimeValue.int valType.bitwidth fv) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int valType.bitwidth (Data.LLVM.Int.select c tv fv)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 3 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvalEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvalEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
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
  obtain ⟨tvalv, htvalv⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  obtain ⟨fvalv, hfvalv⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 2 hsize2
  have hcGetVar : state.variables.getVar? cond = some cval := by
    rw [hCondEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hcval
  have htGetVar : state.variables.getVar? tval = some tvalv := by
    rw [hTvalEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact htvalv
  have hfGetVar : state.variables.getVar? fval = some fvalv := by
    rw [hFvalEq, show (op.getOperands! ctx.raw)[2]! = (op.getOperands! ctx.raw)[2] from by grind]
    exact hfvalv
  have hcconf := VariableState.getVar?_conforms hcGetVar
  rw [show cond.getType! ctx.raw = ⟨.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩
        from Subtype.ext hCondType] at hcconf
  obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType hcconf
  have htconf := VariableState.getVar?_conforms htGetVar
  rw [show tval.getType! ctx.raw = ⟨.integerType valType, hTvalType ▸ (tval.getType! ctx.raw).2⟩
        from Subtype.ext hTvalType] at htconf
  obtain ⟨tv, rfl⟩ := RuntimeValue.Conforms.integerType htconf
  have hfconf := VariableState.getVar?_conforms hfGetVar
  rw [show fval.getType! ctx.raw = ⟨.integerType valType, hFvalType ▸ (fval.getType! ctx.raw).2⟩
        from Subtype.ext hFvalType] at hfconf
  obtain ⟨fv, rfl⟩ := RuntimeValue.Conforms.integerType hfconf
  refine ⟨c, tv, fv, hcGetVar, htGetVar, hfGetVar, ?_⟩
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int 1 c, RuntimeValue.int valType.bitwidth tv,
          RuntimeValue.int valType.bitwidth fv] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hcGetVar
    | 1, _ => simpa [hOperand1] using htGetVar
    | 2, _ => simpa [hOperand2] using hfGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int valType.bitwidth (Data.LLVM.Int.select c tv fv)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-! ### Data-level refinement lemmas -/

/-- `select c t 0 → czero.eqz t, c` at `i64` (with operand refinement). -/
theorem select_czeroeqz_isRefinedBy_toInt_64 {c ct : Data.LLVM.Int 1} {t tt : Data.LLVM.Int 64}
    (hc : c ⊒ ct) (ht : t ⊒ tt) :
    Data.LLVM.Int.select c t (Data.LLVM.Int.constant 64 0)
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt)) 64 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono t (Data.LLVM.Int.constant 64 0) tt (Data.LLVM.Int.constant 64 0) c ct ht
      (isRefinedBy_refl _) hc)
    (by veir_bv_decide)

/-- `select c t 0 → czero.eqz t, c` at `i32` (with operand refinement). -/
theorem select_czeroeqz_isRefinedBy_toInt_32 {c ct : Data.LLVM.Int 1} {t tt : Data.LLVM.Int 32}
    (hc : c ⊒ ct) (ht : t ⊒ tt) :
    Data.LLVM.Int.select c t (Data.LLVM.Int.constant 32 0)
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt)) 32 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono t (Data.LLVM.Int.constant 32 0) tt (Data.LLVM.Int.constant 32 0) c ct ht
      (isRefinedBy_refl _) hc)
    (by veir_bv_decide)

/-- `select c 0 f → czero.nez f, c` at `i64` (with operand refinement). -/
theorem select_czeronez_isRefinedBy_toInt_64 {c ct : Data.LLVM.Int 1} {f ft : Data.LLVM.Int 64}
    (hc : c ⊒ ct) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c (Data.LLVM.Int.constant 64 0) f
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft)) 64 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono (Data.LLVM.Int.constant 64 0) f (Data.LLVM.Int.constant 64 0) ft c ct
      (isRefinedBy_refl _) hf hc)
    (by veir_bv_decide)

/-- `select c 0 f → czero.nez f, c` at `i32` (with operand refinement). -/
theorem select_czeronez_isRefinedBy_toInt_32 {c ct : Data.LLVM.Int 1} {f ft : Data.LLVM.Int 32}
    (hc : c ⊒ ct) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c (Data.LLVM.Int.constant 32 0) f
      ⊒ RISCV.Reg.toInt (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft)) 32 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono (Data.LLVM.Int.constant 32 0) f (Data.LLVM.Int.constant 32 0) ft c ct
      (isRefinedBy_refl _) hf hc)
    (by veir_bv_decide)

/-- `select c t f → or (czero.eqz t c) (czero.nez f c)` at `i64` (with operand refinement). -/
theorem select_general_isRefinedBy_toInt_64 {c ct : Data.LLVM.Int 1} {t tt f ft : Data.LLVM.Int 64}
    (hc : c ⊒ ct) (ht : t ⊒ tt) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c t f
      ⊒ RISCV.Reg.toInt (Data.RISCV.or (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))) 64 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono t f tt ft c ct ht hf hc)
    (by veir_bv_decide)

/-- `select c t f → or (czero.eqz t c) (czero.nez f c)` at `i32` (with operand refinement). -/
theorem select_general_isRefinedBy_toInt_32 {c ct : Data.LLVM.Int 1} {t tt f ft : Data.LLVM.Int 32}
    (hc : c ⊒ ct) (ht : t ⊒ tt) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c t f
      ⊒ RISCV.Reg.toInt (Data.RISCV.or (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))) 32 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono t f tt ft c ct ht hf hc)
    (by veir_bv_decide)

/-- `select c t f → or (czero.eqz t c) (czero.nez f c)` at `i1` (with operand refinement). -/
theorem select_general_isRefinedBy_toInt_1 {c ct : Data.LLVM.Int 1} {t tt f ft : Data.LLVM.Int 1}
    (hc : c ⊒ ct) (ht : t ⊒ tt) (hf : f ⊒ ft) :
    Data.LLVM.Int.select c t f
      ⊒ RISCV.Reg.toInt (Data.RISCV.or (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.select_mono t f tt ft c ct ht hf hc)
    (by veir_bv_decide)

/-! ### Correctness of `selectCzeroeqz_local` -/

set_option maxHeartbeats 1600000 in
/-- Correctness of the `selectCzeroeqz_local` lowering: the
    `castToReg → castToReg → czeroeqz → castBack` round trip refines `llvm.select c t 0`. -/
theorem selectCzeroeqz_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics selectCzeroeqz_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectCzeroeqz_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hCondI1, hTvalFvalEq, hResTvalEq⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  obtain ⟨i1ty, hCondTyVal, hi1w⟩ := hCondI1
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvalEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvalEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be an integer type (else the destructure returns `none`).
  obtain ⟨retIntTy, hResTyVal⟩ :
      ∃ t : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hR : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hR] at hpattern; simp at hpattern
  rw [hResTyVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false.
  peelSplittableCondition [hBw] hpattern
  -- Operand and result types.
  obtain ⟨i1bw⟩ := i1ty; simp only at hi1w; subst hi1w
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    rw [← hOperand0]; exact hCondTyVal
  have hTvalType : (tval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand1, ← hTvalFvalEq]; exact hResTyVal
  have hFvalType : (fval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand2, ← hResTvalEq]; exact hResTyVal
  have hResType : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType retIntTy, by grind⟩ :=
    Subtype.ext hResTyVal
  -- Peel the zero-constant match on the false arm.
  have hCZSome : (matchConstantZero fval ctx.raw).isSome := by
    cases hCZ : matchConstantZero fval ctx.raw with
    | some y => rfl
    | none => rw [hCZ] at hpattern; simp at hpattern
  obtain ⟨_, hCZ⟩ := Option.isSome_iff_exists.mp hCZSome
  rw [hCZ] at hpattern
  simp only [] at hpattern
  obtain ⟨-, attr, hCstVal, hAttrZero⟩ := matchConstantZero_implies hCZ
  -- Unfold the interpretation of the matched `select`.
  obtain ⟨cVal, tvVal, fvVal, hcVal, htvVal, hfvVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hCondType hTvalType
      hFvalType hinterp
  subst hCf
  -- Pin the false arm's runtime value to the zero constant via `EquationLemmaAt`.
  have hfvConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCstVal (by rw [hOperands]; simp) hFvalType
  rw [hAttrZero] at hfvConst
  obtain rfl : fvVal = Data.LLVM.Int.constant retIntTy.bitwidth 0 := by
    have h := hfvVal.symm.trans hfvConst; simpa using h
  -- Both cast operands dominate the rewrite point in the source context.
  have hDomCtxT : tval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `select` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have tNotOp : ¬ tval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two casts, transporting both operand dominance facts through each.
  peelCastToRegLocal₂ hpattern ctx₁ tCastOp hTCast hDomCtxT hDomT₁ hDomCtxC hDomC₁
  peelCastToRegLocal₂ hpattern ctx₂ condCastOp hCCast hDomT₁ hDomT₂ hDomC₁ hDomC₂
  -- Freshness facts for the frame clauses.
  have hTCastFresh : ¬ tCastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds tCastOp hTCast
  have hCondIn : cond.InBounds ctx.raw := by clear hpattern; grind
  have hCondNeTCastRes : ∀ i, cond ≠ ValuePtr.opResult (tCastOp.getResult i) := by
    intro i heq
    rw [heq] at hCondIn
    rw [ValuePtr.inBounds_opResult] at hCondIn
    obtain ⟨hIn, -⟩ := hCondIn
    exact hTCastFresh hIn
  -- Peel the `czeroeqz` and the `replaceWithRegLocal`.
  peelOpCreation!₂ hpattern ctx₃ czOp hCz hDomT₂ hDomT₃ hDomC₂ hDomC₃
  peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomT₃ hDomT₄ hDomC₃ hDomC₄
  cleanupHpattern hpattern
  -- Read the refined values `tt`/`ct` in the target state `state'`.
  obtain ⟨tt, hTVal', httRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) htvVal
      hDomCtxT hDomT₄ tNotOp
  obtain ⟨ct, hCVal', hctRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
      hDomCtxC hDomC₄ cNotOp
  -- Structural facts about the four created ops.
  have hTCastType : tCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCCastType : condCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzType : czOp.getOpType! ctx₄.raw = .riscv .czeroeqz := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hTCastOperands : tCastOp.getOperands! ctx₄.raw = #[tval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCCastOperands : condCastOp.getOperands! ctx₄.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzOperands : czOp.getOperands! ctx₄.raw
      = #[ValuePtr.opResult (tCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (czOp.getResult 0)] := by grind
  -- The cast-back op's result type is `i{retW}`.
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType retIntTy, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hCz
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hTCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hTCastResTypes : tCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hCCastResTypes : condCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzResTypes : czOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType retIntTy, by grind⟩] := by grind
  -- Freshness facts for the frame clauses.
  have hCondNotTCastRes : cond ∉ tCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw cond tCastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hCondNeTCastRes i)
  have hTCastNotCCastRes :
      ValuePtr.opResult (tCastOp.getResult 0) ∉ condCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
        (ValuePtr.opResult (tCastOp.getResult 0)) condCastOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  -- Interpretation tail in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hTCastType hTCastOperands hTCastResTypes hTVal'
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond hCondNotTCastRes]; exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hCCastType hCCastOperands hCCastResTypes hCVal₁
  have hTRes₂ : s₂.variables.getVar? (ValuePtr.opResult (tCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg tt)) := by
    rw [hFrame₂ _ hTCastNotCCastRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl) hCzType hCzOperands
      hCzResTypes hTRes₂ hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))
          retIntTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · apply RuntimeValue.arrayIsRefinedBy_singleton.mpr
      refine ⟨rfl, ?_⟩
      obtain ⟨rbw⟩ := retIntTy; simp only at hBw
      rcases (show rbw = 64 ∨ rbw = 32 by omega) with h | h <;> subst h
      · simpa using select_czeroeqz_isRefinedBy_toInt_64 hctRef httRef
      · simpa using select_czeroeqz_isRefinedBy_toInt_32 hctRef httRef

/-! ### Correctness of `selectCzeronez_local` -/

set_option maxHeartbeats 1600000 in
/-- Correctness of the `selectCzeronez_local` lowering: the
    `castToReg → castToReg → czeronez → castBack` round trip refines `llvm.select c 0 f`. -/
theorem selectCzeronez_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics selectCzeronez_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectCzeronez_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hCondI1, hTvalFvalEq, hResTvalEq⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  obtain ⟨i1ty, hCondTyVal, hi1w⟩ := hCondI1
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvalEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvalEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be an integer type (else the destructure returns `none`).
  obtain ⟨retIntTy, hResTyVal⟩ :
      ∃ t : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hR : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hR] at hpattern; simp at hpattern
  rw [hResTyVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false.
  peelSplittableCondition [hBw] hpattern
  -- Operand and result types.
  obtain ⟨i1bw⟩ := i1ty; simp only at hi1w; subst hi1w
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    rw [← hOperand0]; exact hCondTyVal
  have hTvalType : (tval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand1, ← hTvalFvalEq]; exact hResTyVal
  have hFvalType : (fval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand2, ← hResTvalEq]; exact hResTyVal
  have hResType : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType retIntTy, by grind⟩ :=
    Subtype.ext hResTyVal
  -- Peel the zero-constant match on the true arm.
  have hCZSome : (matchConstantZero tval ctx.raw).isSome := by
    cases hCZ : matchConstantZero tval ctx.raw with
    | some y => rfl
    | none => rw [hCZ] at hpattern; simp at hpattern
  obtain ⟨_, hCZ⟩ := Option.isSome_iff_exists.mp hCZSome
  rw [hCZ] at hpattern
  simp only [] at hpattern
  obtain ⟨-, attr, hCstVal, hAttrZero⟩ := matchConstantZero_implies hCZ
  -- Unfold the interpretation of the matched `select`.
  obtain ⟨cVal, tvVal, fvVal, hcVal, htvVal, hfvVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hCondType hTvalType
      hFvalType hinterp
  subst hCf
  -- Pin the true arm's runtime value to the zero constant via `EquationLemmaAt`.
  have htvConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCstVal (by rw [hOperands]; simp) hTvalType
  rw [hAttrZero] at htvConst
  obtain rfl : tvVal = Data.LLVM.Int.constant retIntTy.bitwidth 0 := by
    have h := htvVal.symm.trans htvConst; simpa using h
  -- Both cast operands dominate the rewrite point in the source context.
  have hDomCtxF : fval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `select` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have fNotOp : ¬ fval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the two casts, transporting both operand dominance facts through each.
  peelCastToRegLocal₂ hpattern ctx₁ fCastOp hFCast hDomCtxF hDomF₁ hDomCtxC hDomC₁
  peelCastToRegLocal₂ hpattern ctx₂ condCastOp hCCast hDomF₁ hDomF₂ hDomC₁ hDomC₂
  -- Freshness facts for the frame clauses.
  have hFCastFresh : ¬ fCastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds fCastOp hFCast
  have hCondIn : cond.InBounds ctx.raw := by clear hpattern; grind
  have hCondNeFCastRes : ∀ i, cond ≠ ValuePtr.opResult (fCastOp.getResult i) := by
    intro i heq
    rw [heq] at hCondIn
    rw [ValuePtr.inBounds_opResult] at hCondIn
    obtain ⟨hIn, -⟩ := hCondIn
    exact hFCastFresh hIn
  -- Peel the `czeronez` and the `replaceWithRegLocal`.
  peelOpCreation!₂ hpattern ctx₃ czOp hCz hDomF₂ hDomF₃ hDomC₂ hDomC₃
  peelReplaceWithRegLocal₂ hpattern ctx₄ castBackOp hCastBack hDomF₃ hDomF₄ hDomC₃ hDomC₄
  cleanupHpattern hpattern
  -- Read the refined values `ft`/`ct` in the target state `state'`.
  obtain ⟨ft, hFVal', hftRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hfvVal
      hDomCtxF hDomF₄ fNotOp
  obtain ⟨ct, hCVal', hctRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hcVal
      hDomCtxC hDomC₄ cNotOp
  -- Structural facts about the four created ops.
  have hFCastType : fCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastType : condCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzType : czOp.getOpType! ctx₄.raw = .riscv .czeronez := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hFCastOperands : fCastOp.getOperands! ctx₄.raw = #[fval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastOperands : condCastOp.getOperands! ctx₄.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzOperands : czOp.getOperands! ctx₄.raw
      = #[ValuePtr.opResult (fCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (czOp.getResult 0)] := by grind
  -- The cast-back op's result type is `i{retW}`.
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType retIntTy, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hCz
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hFCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hFCastResTypes : fCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastResTypes : condCastOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hCzResTypes : czOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCz (operation := czOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := czOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType retIntTy, by grind⟩] := by grind
  -- Freshness facts for the frame clauses.
  have hCondNotFCastRes : cond ∉ fCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw cond fCastOp
      with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hCondNeFCastRes i)
  have hFCastNotCCastRes :
      ValuePtr.opResult (fCastOp.getResult 0) ∉ condCastOp.getResults! ctx₄.raw := by
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₄.raw
        (ValuePtr.opResult (fCastOp.getResult 0)) condCastOp with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (by grind [OperationPtr.getResult])
  -- Interpretation tail in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hFCastType hFCastOperands hFCastResTypes hFVal'
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond hCondNotFCastRes]; exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hCCastType hCCastOperands hCCastResTypes hCVal₁
  have hFRes₂ : s₂.variables.getVar? (ValuePtr.opResult (fCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg ft)) := by
    rw [hFrame₂ _ hFCastNotCCastRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₂) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl) hCzType hCzOperands
      hCzResTypes hFRes₂ hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          retIntTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · apply RuntimeValue.arrayIsRefinedBy_singleton.mpr
      refine ⟨rfl, ?_⟩
      obtain ⟨rbw⟩ := retIntTy; simp only at hBw
      rcases (show rbw = 64 ∨ rbw = 32 by omega) with h | h <;> subst h
      · simpa using select_czeronez_isRefinedBy_toInt_64 hctRef hftRef
      · simpa using select_czeronez_isRefinedBy_toInt_32 hctRef hftRef

/-! ### Correctness of `selectGeneral_local` -/

set_option maxHeartbeats 3200000 in
/-- Correctness of the `selectGeneral_local` lowering: the branchless
    `castToReg → castToReg → castToReg → czeroeqz → czeronez → or → castBack` round trip refines
    `llvm.select c t f`. Both arms are arbitrary (no zero-constant match), so all three operands are
    cast to registers. -/
theorem selectGeneral_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics selectGeneral_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectGeneral_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic and verification facts.
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hCondI1, hTvalFvalEq, hResTvalEq⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  obtain ⟨i1ty, hCondTyVal, hi1w⟩ := hCondI1
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvalEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvalEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The result type must be an integer type (else the destructure returns `none`).
  obtain ⟨retIntTy, hResTyVal⟩ :
      ∃ t : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hR : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hR] at hpattern; simp at hpattern
  rw [hResTyVal] at hpattern
  simp only [] at hpattern
  -- The bitwidth guard must be false.
  peelSplittableCondition [hBw] hpattern
  -- Operand and result types.
  obtain ⟨i1bw⟩ := i1ty; simp only at hi1w; subst hi1w
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    rw [← hOperand0]; exact hCondTyVal
  have hTvalType : (tval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand1, ← hTvalFvalEq]; exact hResTyVal
  have hFvalType : (fval.getType! ctx.raw).val = Attribute.integerType retIntTy := by
    rw [← hOperand2, ← hResTvalEq]; exact hResTyVal
  have hResType : ((op.getResult 0).get! ctx.raw).type = ⟨Attribute.integerType retIntTy, by grind⟩ :=
    Subtype.ext hResTyVal
  -- Unfold the interpretation of the matched `select`.
  obtain ⟨cVal, tvVal, fvVal, hcVal, htvVal, hfvVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hCondType hTvalType
      hFvalType hinterp
  subst hCf
  -- In-bounds facts for the three operands. Established *before* any op creation so `grind` proves
  -- them cheaply; deriving them later (with all seven creation hypotheses in scope) blows the
  -- `createOp_inBounds_mono` E-matching budget.
  have hTvalIn : tval.InBounds ctx.raw := by grind
  have hFvalIn : fval.InBounds ctx.raw := by grind
  have hCondIn : cond.InBounds ctx.raw := by grind
  -- The three operands dominate the rewrite point in the source context.
  have hDomCtxT : tval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxF : fval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `select` of its operands.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have tNotOp : ¬ tval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have fNotOp : ¬ fval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the three casts, transporting all three operand dominance facts through each.
  peelCastToRegLocal₃ hpattern ctx₁ tCastOp hTCast hDomCtxT hDomT₁ hDomCtxF hDomF₁ hDomCtxC hDomC₁
  peelCastToRegLocal₃ hpattern ctx₂ fCastOp hFCast hDomT₁ hDomT₂ hDomF₁ hDomF₂ hDomC₁ hDomC₂
  peelCastToRegLocal₃ hpattern ctx₃ condCastOp hCCast hDomT₂ hDomT₃ hDomF₂ hDomF₃ hDomC₂ hDomC₃
  -- Peel the `czeroeqz` with the macro (dominance transports still shallow enough for `grind`).
  peelOpCreation!₃ hpattern ctx₄ eqzOp hEqz hDomT₃ hDomT₄ hDomF₃ hDomF₄ hDomC₃ hDomC₄
  -- Peel `nezOp`, `orOp` and the cast-back manually. Their operand/`op`-in-bounds facts sit several
  -- creations deep, and `grind` chaining `createOp_inBounds_mono` over all the creation hypotheses
  -- blows past its E-matching budget (and adding any `InBounds` hypothesis to the context poisons the
  -- surrounding `grind`s). So build every `InBounds` witness inline and clear it before continuing.
  have hOpIn₃ : op.InBounds ctx₃.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hCCast
      (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hFCast
        (WfRewriter.createOp_inBounds_mono (ptr := .operation op) hTCast opInBounds))
  have hOpIn₄ : op.InBounds ctx₄.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hEqz hOpIn₃
  -- `nezOp`: operands `#[fCast.getResult 0, condCast.getResult 0]`, both in bounds in `ctx₄`.
  have ⟨⟨ctx₅, nezOp⟩, hNez, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  rw [WfRewriter.createOp!_none_eq
    (by clear hpattern; intro oper ho
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · have hIn : fCastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation fCastOp) hEqz
              (WfRewriter.createOp_inBounds_mono (ptr := .operation fCastOp) hCCast
                (WfRewriter.createOp_new_inBounds fCastOp hFCast))
          have hNum : fCastOp.getNumResults! ctx₄.raw = 1 := by
            grind [OperationPtr.getNumResults!_WfRewriter_createOp hFCast (operation := fCastOp),
              OperationPtr.getNumResults!_WfRewriter_createOp hCCast (operation := fCastOp),
              OperationPtr.getNumResults!_WfRewriter_createOp hEqz (operation := fCastOp)]
          grind
        · have hIn : condCastOp.InBounds ctx₄.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation condCastOp) hEqz
              (WfRewriter.createOp_new_inBounds condCastOp hCCast)
          have hNum : condCastOp.getNumResults! ctx₄.raw = 1 := by
            grind [OperationPtr.getNumResults!_WfRewriter_createOp hCCast (operation := condCastOp),
              OperationPtr.getNumResults!_WfRewriter_createOp hEqz (operation := condCastOp)]
          grind)
    (by clear hpattern; simp) (by clear hpattern; simp)] at hNez
  have hOpNeNez : op ≠ nezOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds nezOp hNez (heq ▸ hOpIn₄)
  have hDomT₅ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hNez hOpIn₄ hOpNeNez).mpr hDomT₄
  have hDomF₅ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hNez hOpIn₄ hOpNeNez).mpr hDomF₄
  have hDomC₅ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hNez hOpIn₄ hOpNeNez).mpr hDomC₄
  have hOpIn₅ : op.InBounds ctx₅.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hNez hOpIn₄
  clear hOpNeNez
  -- `orOp`: operands `#[eqz.getResult 0, nez.getResult 0]`, both in bounds in `ctx₅`.
  have ⟨⟨ctx₆, orOp⟩, hOr, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  rw [WfRewriter.createOp!_none_eq
    (by clear hpattern; intro oper ho
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · have hIn : eqzOp.InBounds ctx₅.raw :=
            WfRewriter.createOp_inBounds_mono (ptr := .operation eqzOp) hNez
              (WfRewriter.createOp_new_inBounds eqzOp hEqz)
          have hNum : eqzOp.getNumResults! ctx₅.raw = 1 := by
            grind [OperationPtr.getNumResults!_WfRewriter_createOp hEqz (operation := eqzOp),
              OperationPtr.getNumResults!_WfRewriter_createOp hNez (operation := eqzOp)]
          grind
        · have hIn : nezOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds nezOp hNez
          have hNum : nezOp.getNumResults! ctx₅.raw = 1 := by
            grind [OperationPtr.getNumResults!_WfRewriter_createOp hNez (operation := nezOp)]
          grind)
    (by clear hpattern; simp) (by clear hpattern; simp)] at hOr
  have hOpNeOr : op ≠ orOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds orOp hOr (heq ▸ hOpIn₅)
  have hDomT₆ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOr hOpIn₅ hOpNeOr).mpr hDomT₅
  have hDomF₆ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOr hOpIn₅ hOpNeOr).mpr hDomF₅
  have hDomC₆ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hOr hOpIn₅ hOpNeOr).mpr hDomC₅
  have hOpIn₆ : op.InBounds ctx₆.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .operation op) hOr hOpIn₅
  clear hOpNeOr
  -- Cast-back (`replaceWithRegLocal`): operand `#[or.getResult 0]`, in bounds in `ctx₆`.
  have ⟨⟨ctx₇, castBackOp⟩, hCastBack, pat'⟩ := hpattern
  clear hpattern; have hpattern := pat'; clear pat'
  simp only [replaceWithRegLocal] at hCastBack
  rw [WfRewriter.createOp!_none_eq
    (by clear hpattern; intro oper ho
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl
        have hIn : orOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds orOp hOr
        have hNum : orOp.getNumResults! ctx₆.raw = 1 := by
          grind [OperationPtr.getNumResults!_WfRewriter_createOp hOr (operation := orOp)]
        grind)
    (by clear hpattern; simp) (by clear hpattern; simp)] at hCastBack
  have hOpNeCB : op ≠ castBackOp := fun heq =>
    WfRewriter.createOp_new_not_inBounds castBackOp hCastBack (heq ▸ hOpIn₆)
  have hDomT₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpIn₆ hOpNeCB).mpr hDomT₆
  have hDomF₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpIn₆ hOpNeCB).mpr hDomF₆
  have hDomC₇ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack hOpIn₆ hOpNeCB).mpr hDomC₆
  clear hOpIn₃ hOpIn₄ hOpIn₅ hOpIn₆ hOpNeCB
  cleanupHpattern hpattern
  -- Read the refined values `tt`/`ft`/`ct` in the target state `state'`.
  obtain ⟨tt, hTVal', httRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTvalIn htvVal
      hDomCtxT hDomT₇ tNotOp
  obtain ⟨ft, hFVal', hftRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFvalIn hfvVal
      hDomCtxF hDomF₇ fNotOp
  obtain ⟨ct, hCVal', hctRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCondIn hcVal
      hDomCtxC hDomC₇ cNotOp
  -- Structural facts about the seven created ops.
  have hTCastType : tCastOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hFCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hEqz (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hNez (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := tCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hFCastType : fCastOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hEqz (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hNez (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := fCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastType : condCastOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hEqz (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hNez (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := condCastOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hEqzType : eqzOp.getOpType! ctx₇.raw = .riscv .czeroeqz := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hEqz (operation := eqzOp),
      OperationPtr.getOpType!_WfRewriter_createOp hNez (operation := eqzOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := eqzOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := eqzOp)]
  have hNezType : nezOp.getOpType! ctx₇.raw = .riscv .czeronez := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNez (operation := nezOp),
      OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := nezOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := nezOp)]
  have hOrType : orOp.getOpType! ctx₇.raw = .riscv .or := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackType : castBackOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hTCastOperands : tCastOp.getOperands! ctx₇.raw = #[tval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hFCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hEqz (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hNez (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := tCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hFCastOperands : fCastOp.getOperands! ctx₇.raw = #[fval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hEqz (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hNez (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := fCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastOperands : condCastOp.getOperands! ctx₇.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hEqz (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hNez (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := condCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hEqzOperands : eqzOp.getOperands! ctx₇.raw
      = #[ValuePtr.opResult (tCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hEqz (operation := eqzOp),
      OperationPtr.getOperands!_WfRewriter_createOp hNez (operation := eqzOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := eqzOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := eqzOp)]
  have hNezOperands : nezOp.getOperands! ctx₇.raw
      = #[ValuePtr.opResult (fCastOp.getResult 0), ValuePtr.opResult (condCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNez (operation := nezOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := nezOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := nezOp)]
  have hOrOperands : orOp.getOperands! ctx₇.raw
      = #[ValuePtr.opResult (eqzOp.getResult 0), ValuePtr.opResult (nezOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (orOp.getResult 0)] := by grind
  -- The cast-back op's result type is `i{retW}`.
  have hCBType : ((op.getResult 0).get! ctx₆.raw).type
      = (⟨Attribute.integerType retIntTy, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₆.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hOr
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hNez
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hEqz
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hFCast
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hTCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simpa only [ValuePtr.getType!_opResult, hResType] using h1
  have hTCastResTypes : tCastOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hTCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hFCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hEqz (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hNez (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := tCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := tCastOp)]
  have hFCastResTypes : fCastOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hFCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hEqz (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hNez (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := fCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := fCastOp)]
  have hCCastResTypes : condCastOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCCast (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hEqz (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hNez (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := condCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := condCastOp)]
  have hEqzResTypes : eqzOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hEqz (operation := eqzOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hNez (operation := eqzOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := eqzOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := eqzOp)]
  have hNezResTypes : nezOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hNez (operation := nezOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := nezOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := nezOp)]
  have hOrResTypes : orOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := orOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.integerType retIntTy, by grind⟩] := by grind
  -- Freshness of the source operands relative to the fresh cast results.
  have hTCastFresh : ¬ tCastOp.InBounds ctx.raw :=
    WfRewriter.createOp_new_not_inBounds tCastOp hTCast
  have hFCastFresh : ¬ fCastOp.InBounds ctx.raw := by
    grind [WfRewriter.createOp_new_not_inBounds fCastOp hFCast,
      WfRewriter.createOp_inBounds_mono hTCast]
  have srcNeFreshRes : ∀ (s : ValuePtr) (o : OperationPtr), s.InBounds ctx.raw →
      ¬ o.InBounds ctx.raw → ∀ i, s ≠ ValuePtr.opResult (o.getResult i) := by
    intro s o hsIn hoFresh i heq
    rw [heq, ValuePtr.inBounds_opResult] at hsIn
    exact hoFresh hsIn.1
  -- Freshness facts (non-membership in results) for the frame clauses.
  have notMemRes : ∀ (v : ValuePtr) (o : OperationPtr),
      (∀ i, v ≠ ValuePtr.opResult (o.getResult i)) → v ∉ o.getResults! ctx₇.raw := by
    intro v o hne
    rcases OperationPtr.getResults!_not_mem_or_eq_getResult ctx₇.raw v o with hres | ⟨i, hi, heq⟩
    · exact hres
    · exact absurd heq (hne i)
  have hFvalNotTCastRes : fval ∉ tCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (srcNeFreshRes fval tCastOp hFvalIn hTCastFresh)
  have hCondNotTCastRes : cond ∉ tCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (srcNeFreshRes cond tCastOp hCondIn hTCastFresh)
  have hCondNotFCastRes : cond ∉ fCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (srcNeFreshRes cond fCastOp hCondIn hFCastFresh)
  have hTCastNotFCastRes :
      ValuePtr.opResult (tCastOp.getResult 0) ∉ fCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hTCastNotCCastRes :
      ValuePtr.opResult (tCastOp.getResult 0) ∉ condCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hFCastNotCCastRes :
      ValuePtr.opResult (fCastOp.getResult 0) ∉ condCastOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hTCastNotEqzRes :
      ValuePtr.opResult (tCastOp.getResult 0) ∉ eqzOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hFCastNotEqzRes :
      ValuePtr.opResult (fCastOp.getResult 0) ∉ eqzOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hCCastNotEqzRes :
      ValuePtr.opResult (condCastOp.getResult 0) ∉ eqzOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hFCastNotNezRes :
      ValuePtr.opResult (fCastOp.getResult 0) ∉ nezOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hCCastNotNezRes :
      ValuePtr.opResult (condCastOp.getResult 0) ∉ nezOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hEqzNotNezRes :
      ValuePtr.opResult (eqzOp.getResult 0) ∉ nezOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  have hEqzNotOrRes :
      ValuePtr.opResult (eqzOp.getResult 0) ∉ orOp.getResults! ctx₇.raw :=
    notMemRes _ _ (fun i => by grind [OperationPtr.getResult])
  -- Interpretation tail: `[tCast, fCast, condCast, eqz, nez, or, castBack]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hTCastType hTCastOperands hTCastResTypes hTVal'
  have hFVal₁ : s₁.variables.getVar? fval = some (RuntimeValue.int retIntTy.bitwidth ft) := by
    rw [hFrame₁ fval hFvalNotTCastRes]; exact hFVal'
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond hCondNotTCastRes]; exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_castToReg_forward (state := s₁) (inBounds := by grind)
      hFCastType hFCastOperands hFCastResTypes hFVal₁
  have hCVal₂ : s₂.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₂ cond hCondNotFCastRes]; exact hCVal₁
  have hTRes₂ : s₂.variables.getVar? (ValuePtr.opResult (tCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg tt)) := by
    rw [hFrame₂ _ hTCastNotFCastRes]; exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
    interpretOp_castToReg_forward (state := s₂) (inBounds := by grind)
      hCCastType hCCastOperands hCCastResTypes hCVal₂
  have hTRes₃ : s₃.variables.getVar? (ValuePtr.opResult (tCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg tt)) := by
    rw [hFrame₃ _ hTCastNotCCastRes]; exact hTRes₂
  have hFRes₃ : s₃.variables.getVar? (ValuePtr.opResult (fCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg ft)) := by
    rw [hFrame₃ _ hFCastNotCCastRes]; exact hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₃) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeroeqz r₂ r₁) (fun _ _ _ _ => rfl) hEqzType hEqzOperands
      hEqzResTypes hTRes₃ hRes₃
  have hFRes₄ : s₄.variables.getVar? (ValuePtr.opResult (fCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg ft)) := by
    rw [hFrame₄ _ hFCastNotEqzRes]; exact hFRes₃
  have hCRes₄ : s₄.variables.getVar? (ValuePtr.opResult (condCastOp.getResult 0))
      = some (RuntimeValue.reg (LLVM.Int.toReg ct)) := by
    rw [hFrame₄ _ hCCastNotEqzRes]; exact hRes₃
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₄) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.czeronez r₂ r₁) (fun _ _ _ _ => rfl) hNezType hNezOperands
      hNezResTypes hFRes₄ hCRes₄
  have hEqzRes₅ : s₅.variables.getVar? (ValuePtr.opResult (eqzOp.getResult 0))
      = some (RuntimeValue.reg (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))) := by
    rw [hFrame₅ _ hEqzNotNezRes]; exact hRes₄
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₅) (inBounds := by grind)
      (f := fun r₁ r₂ => Data.RISCV.or r₂ r₁) (fun _ _ _ _ => rfl) hOrType hOrOperands
      hOrResTypes hEqzRes₅ hRes₅
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, -⟩ :=
    interpretOp_castBack_forward (state := s₆) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₆
  refine ⟨s₇, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, hI₅, hI₆, hI₇, liftM, monadLift,
      MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retIntTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.or (Data.RISCV.czeronez (LLVM.Int.toReg ct) (LLVM.Int.toReg ft))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg ct) (LLVM.Int.toReg tt))) retIntTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₇, Option.bind, Option.map]
    · apply RuntimeValue.arrayIsRefinedBy_singleton.mpr
      refine ⟨rfl, ?_⟩
      obtain ⟨rbw⟩ := retIntTy; simp only at hBw
      rcases (show rbw = 64 ∨ rbw = 32 ∨ rbw = 1 by omega) with h | h | h <;> subst h
      · simpa using select_general_isRefinedBy_toInt_64 hctRef httRef hftRef
      · simpa using select_general_isRefinedBy_toInt_32 hctRef httRef hftRef
      · simpa using select_general_isRefinedBy_toInt_1 hctRef httRef hftRef

end Veir
