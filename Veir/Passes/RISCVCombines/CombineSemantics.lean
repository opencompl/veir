import Veir.Passes.RISCVCombines.Combine
import Veir.Passes.RISCVCombines.LLVMProofs
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
import Veir.Passes.InstructionSelection.RewriteProofs.LowerExt
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSlti
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics

/-!
  Graph-level semantics preservation for the LLVM-dialect combines.

  `LLVMProofs.lean` proves the *data-level* obligation of each combine: an
  `⊒` refinement between `Data.LLVM.Int` terms. That is only half the story — nothing
  there ties a theorem to the rewrite of the same name. This file closes the gap for the
  combines that have been ported to `LocalRewritePattern` form, by proving
  `LocalRewritePattern.PreservesSemantics` for each, which is a statement *about the
  pattern function itself*.

  Two shapes appear here.

  * The value-replacement combines create no operations at all: their local pattern
    returns `(ctx, some (#[], #[v]))`, and `RewritePattern.fromLocalRewrite` performs the
    `replaceValue`/`eraseOp`. `interpretOpList [] state'` is then just `state'`, so the
    proof reduces to transporting the matched operands' refinement through the data lemma.

  * `mulo_by_2_unsigned_signed` creates one operation, and so additionally has to replay
    that operation forward in the target state.

  As in the instruction-selection proofs, the four `Return*` well-formedness predicates of
  the pattern are taken as hypotheses rather than discharged here.

  The patterns carry an `.integerType` guard and a `bitwidth ∈ {32, 64}` guard so that the
  `veir_bv_decide` data lemmas apply; see the `Combine.lean` definitions.
-/

namespace Veir.RISCV

open Veir Veir.Data.LLVM

set_option maxHeartbeats 1000000 in
theorem select_same_val_self_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps select_same_val_self_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges select_same_val_self_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds select_same_val_self_local}
    {h₄ : LocalRewritePattern.ReturnValues select_same_val_self_local} :
    LocalRewritePattern.PreservesSemantics select_same_val_self_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, select_same_val_self_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
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
  -- Result-type guard.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Bitwidth guard.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  -- The `tval = fval` guard.
  have hEq : tval = fval := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hEq] at hpattern
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTValType : (tval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFValType : (fval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  -- Unfold the `select` interpretation.
  obtain ⟨cv, tv, fv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTValType hFValType hinterp
  subst hCf
  have hDomT : tval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have tNotOp : ¬ tval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Nothing is created: `newCtx = ctx`, `newOps = #[]`, `newValues = #[tval]`.
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[tval] := by
    simp at hpattern; grind
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) htVal
      hDomT hDomT tNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth tt], by simp [hTVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  obtain rfl : fv = tv := by
    have h' := hfVal.symm.trans (hEq ▸ htVal)
    simpa using h'
  exact isRefinedBy_trans (by simpa using Data.LLVM.Int.select_same_val_self hWidth (c := cv)) htRef

/-- Shared skeleton for `select_constant_cmp_true`/`_false`: peel the `matchSelect`, the
    type/width guards and the constant-condition match, then pin the condition's runtime
    value to `constant 1 cst.value`. -/
private theorem select_constant_cmp_core {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    (ctxVerif : ctx.Verified) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx} (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {newState : InterpreterState ctx} {cf} {cond tval fval : ValuePtr} {intType : IntegerType}
    {cstVal : Int}
    (hMatch : matchSelect op ctx.raw = some (cond, tval, fval))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType)
    (hCst : (matchConstantIntVal cond ctx.raw).map (·.value) = some cstVal)
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (tv fv : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? tval = some (RuntimeValue.int intType.bitwidth tv) ∧
      state.variables.getVar? fval = some (RuntimeValue.int intType.bitwidth fv) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.select (Data.LLVM.Int.constant 1 cstVal) tv fv)) ∧
      cf = none ∧
      tval.dominatesIp (InsertPoint.before op) ctx ∧
      fval.dominatesIp (InsertPoint.before op) ctx ∧
      ¬ tval ∈ op.getResults! ctx.raw ∧ ¬ fval ∈ op.getResults! ctx.raw ∧
      tval.InBounds ctx.raw ∧ fval.InBounds ctx.raw := by
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
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTValType : (tval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFValType : (fval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  obtain ⟨cv, tv, fv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTValType hFValType hinterp
  -- Pin the condition to the matched constant.
  obtain ⟨intAttr, hCstMatch, hCstEq⟩ : ∃ a, matchConstantIntVal cond ctx.raw = some a ∧
      a.value = cstVal := by
    cases hm : matchConstantIntVal cond ctx.raw with
    | none => rw [hm] at hCst; simp at hCst
    | some a => rw [hm] at hCst; simp at hCst; exact ⟨a, rfl, hCst⟩
  have hcConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hCondType
  obtain rfl : cv = Data.LLVM.Int.constant 1 intAttr.value := by
    have := hcVal.symm.trans hcConstVal; simpa using this
  subst hCstEq
  refine ⟨tv, fv, htVal, hfVal, hMem, hRes, hCf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind [WfIRContext.Dom.operand_dominates_op]
  · grind [WfIRContext.Dom.operand_dominates_op]
  · grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  · grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  · grind
  · grind

set_option maxHeartbeats 1000000 in
theorem select_constant_cmp_true_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps select_constant_cmp_true_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges select_constant_cmp_true_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds select_constant_cmp_true_local}
    {h₄ : LocalRewritePattern.ReturnValues select_constant_cmp_true_local} :
    LocalRewritePattern.PreservesSemantics select_constant_cmp_true_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, select_constant_cmp_true_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  have hCstSome : (matchConstantIntVal cond ctx.raw).isSome := by
    cases hM : matchConstantIntVal cond ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨intAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  have hVal1 : intAttr.value = 1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hVal1] at hpattern
  obtain ⟨tv, fv, htVal, hfVal, hMem, hRes, hCf, hDomT, hDomF, tNotOp, fNotOp, hTIn, hFIn⟩ :=
    select_constant_cmp_core (cstVal := 1) ctxDom ctxVerif opInBounds stateWf hMatch hResType
      (by rw [hCstMatch]; simp [hVal1]) hinterp
  subst hCf
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[tval] := by
    simp at hpattern; grind
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTIn htVal
      hDomT hDomT tNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth tt], by simp [hTVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  exact isRefinedBy_trans
    (by simpa using Data.LLVM.Int.select_constant_cmp_true hWidth (x := tv) (y := fv)) htRef

set_option maxHeartbeats 1000000 in
theorem select_constant_cmp_false_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps select_constant_cmp_false_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges select_constant_cmp_false_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds select_constant_cmp_false_local}
    {h₄ : LocalRewritePattern.ReturnValues select_constant_cmp_false_local} :
    LocalRewritePattern.PreservesSemantics select_constant_cmp_false_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, select_constant_cmp_false_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  have ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  have hCstSome : (matchConstantIntVal cond ctx.raw).isSome := by
    cases hM : matchConstantIntVal cond ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨intAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  have hVal0 : intAttr.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hVal0] at hpattern
  obtain ⟨tv, fv, htVal, hfVal, hMem, hRes, hCf, hDomT, hDomF, tNotOp, fNotOp, hTIn, hFIn⟩ :=
    select_constant_cmp_core (cstVal := 0) ctxDom ctxVerif opInBounds stateWf hMatch hResType
      (by rw [hCstMatch]; simp [hVal0]) hinterp
  subst hCf
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[fval] := by
    simp at hpattern; grind
  obtain ⟨ft, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFIn hfVal
      hDomF hDomF fNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth ft], by simp [hFVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  exact isRefinedBy_trans
    (by simpa using Data.LLVM.Int.select_constant_cmp_false hWidth (x := tv) (y := fv)) hfRef

/-! ### sub_add_reg

  `(x + y) - y -> x` and `(x + y) - x -> y`. Both match the `add` through the `sub`'s
  defining op, so both need the Layer-3 graph lemma `matchAdd_getVar?_of_EquationLemmaAt`
  to recover the `add`'s runtime value from `EquationLemmaAt`.
-/

/-- Shared skeleton for the two `sub_add_reg` combines: peel `matchSub`, the type/width
    guards, the defining `add` and its `matchAdd`, then expose the `add`'s operand values
    together with the matched `sub`'s result value. -/
private theorem sub_add_reg_core {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    (ctxVerif : ctx.Verified) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {newState : InterpreterState ctx} {cf} {s0 s1 x y : ValuePtr} {addOp : OperationPtr}
    {sProps : propertiesOf (.llvm .sub)} {aProps : propertiesOf (.llvm .add)}
    {intType : IntegerType}
    (hMatch : matchSub op ctx.raw = some (s0, s1, sProps))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType)
    (hDef : getDefiningOp s0 ctx.raw = some addOp)
    (hAdd : matchAdd addOp ctx.raw = some (x, y, aProps))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (xv yv s1v : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yv) ∧
      state.variables.getVar? s1 = some (RuntimeValue.int intType.bitwidth s1v) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.sub (Data.LLVM.Int.add xv yv aProps.nsw aProps.nuw) s1v
          sProps.nsw sProps.nuw)) ∧
      cf = none ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ y.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧ y.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw ∧ y ∉ op.getResults! ctx.raw := by
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchSub_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subIntType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hOpType
  have hIntTypeEq : intType = subIntType := by rw [hSubResType] at hResType; grind
  subst hIntTypeEq
  have hs0Eq : s0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hs1Eq : s1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = s0 := by
    rw [hs0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = s1 := by
    rw [hs1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hs0Type : (s0.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hSubOperand0Type]
  have hs1Type : (s1.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hSubOperand1Type]
  -- Unfold the matched `sub`'s interpretation.
  obtain ⟨s0v, s1v, hs0Val, hs1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res h
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h
          grind)
      hinterp hs0Type hs1Type
  -- Recover the defining `add`'s value.
  obtain ⟨xv, yv, hxVal, hyVal, hs0AddVal, hxType, hyType, hDomX, hDomY, hxIn, hyIn,
      hxNotRes, hyNotRes⟩ :=
    matchAdd_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hAdd
      (by rw [hOperands]; simp) hs0Type
  obtain rfl : s0v = Data.LLVM.Int.add xv yv aProps.nsw aProps.nuw := by
    have := hs0Val.symm.trans hs0AddVal; simpa using this
  exact ⟨xv, yv, s1v, hxVal, hyVal, hs1Val, hMem, by rw [hRes, hProps], hCf,
    hDomX, hDomY, hxIn, hyIn, hxNotRes, hyNotRes⟩

set_option maxHeartbeats 1000000 in
theorem sub_add_reg_x_add_y_sub_y_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sub_add_reg_x_add_y_sub_y_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sub_add_reg_x_add_y_sub_y_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sub_add_reg_x_add_y_sub_y_local}
    {h₄ : LocalRewritePattern.ReturnValues sub_add_reg_x_add_y_sub_y_local} :
    LocalRewritePattern.PreservesSemantics sub_add_reg_x_add_y_sub_y_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sub_add_reg_x_add_y_sub_y_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨s0, s1, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchSub_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  have hDefSome : (getDefiningOp s0 ctx.raw).isSome := by
    cases hM : getDefiningOp s0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y, aProps⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  have hEq : y = s1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hEq] at hpattern
  obtain ⟨xv, yv, s1v, hxVal, hyVal, hs1Val, hMem, hRes, hCf, hDomX, hDomY, hxIn, hyIn,
      hxNotRes, hyNotRes⟩ :=
    sub_add_reg_core ctxDom ctxVerif opInBounds stateWf hMatch hResType hDef hAdd hinterp
  subst hCf
  -- `y = s1`, so the subtracted value is the `add`'s right operand.
  have hs1yv : s1v = yv := by
    have h' := hs1Val.symm.trans (hEq ▸ hyVal); simpa using h'
  rw [hs1yv] at hRes
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[x] := by
    simp at hpattern; grind
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX hxNotRes
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth xt], by simp [hXVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  exact isRefinedBy_trans
    (by simpa using Data.LLVM.Int.sub_add_reg_x_add_y_sub_y hWidth (x := xv) (y := yv)) hxRef

set_option maxHeartbeats 1000000 in
theorem sub_add_reg_x_add_y_sub_x_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sub_add_reg_x_add_y_sub_x_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sub_add_reg_x_add_y_sub_x_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sub_add_reg_x_add_y_sub_x_local}
    {h₄ : LocalRewritePattern.ReturnValues sub_add_reg_x_add_y_sub_x_local} :
    LocalRewritePattern.PreservesSemantics sub_add_reg_x_add_y_sub_x_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sub_add_reg_x_add_y_sub_x_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨s0, s1, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchSub_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  have hDefSome : (getDefiningOp s0 ctx.raw).isSome := by
    cases hM : getDefiningOp s0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y, aProps⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  have hEq : x = s1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hEq] at hpattern
  obtain ⟨xv, yv, s1v, hxVal, hyVal, hs1Val, hMem, hRes, hCf, hDomX, hDomY, hxIn, hyIn,
      hxNotRes, hyNotRes⟩ :=
    sub_add_reg_core ctxDom ctxVerif opInBounds stateWf hMatch hResType hDef hAdd hinterp
  subst hCf
  have hs1xv : s1v = xv := by
    have h' := hs1Val.symm.trans (hEq ▸ hxVal); simpa using h'
  rw [hs1xv] at hRes
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[y] := by
    simp at hpattern; grind
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY hyNotRes
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth yt], by simp [hYVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  exact isRefinedBy_trans
    (by simpa using Data.LLVM.Int.sub_add_reg_x_add_y_sub_x hWidth (x := xv) (y := yv)) hyRef

/-! ### mulo_by_2_unsigned_signed — the op-creating exemplar

  `x * 2 -> x + x`. Unlike the value-replacement combines this pattern *creates* an
  operation, so the proof must additionally replay it forward in the target state with
  `interpretOp_llvm_binaryInt_forward`. The `mul`'s `nsw`/`nuw` bundle is reused verbatim
  as the created `add`'s properties, which is sound because at the constant `2` the two ops
  have exactly the same overflow condition (see `Data.LLVM.Int.mulo_by_2_unsigned_signed`).
-/

set_option maxHeartbeats 1000000 in
theorem mulo_by_2_unsigned_signed_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps mulo_by_2_unsigned_signed_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges mulo_by_2_unsigned_signed_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds mulo_by_2_unsigned_signed_local}
    {h₄ : LocalRewritePattern.ReturnValues mulo_by_2_unsigned_signed_local} :
    LocalRewritePattern.PreservesSemantics mulo_by_2_unsigned_signed_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, mulo_by_2_unsigned_signed_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchMul`.
  have hMatchSome : (matchMul op ctx.raw).isSome := by
    cases hM : matchMul op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cval, mp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchMul_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, mulIntType, hMulResType, hMulOperand0Type, hMulOperand1Type⟩ :=
    OperationPtr.Verified.llvm_mul opVerif hOpType
  -- Result-type guard.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hIntTypeEq : intType = mulIntType := by rw [hMulResType] at hResType; grind
  subst hIntTypeEq
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Bitwidth guard.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  -- Constant guard.
  have hCstSome : (matchConstantIntVal cval ctx.raw).isSome := by
    cases hM : matchConstantIntVal cval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨intAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  have hVal2 : intAttr.value = 2 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hVal2] at hpattern
  -- Operand access / types.
  have hxEq : x = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hcEq : cval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = x := by
    rw [hxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = cval := by
    rw [hcEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hMulOperand0Type]
  have hcType : (cval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hMulOperand1Type]
  -- Unfold the matched `mul`'s interpretation.
  obtain ⟨xv, cv, hxVal, hcVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .mul)
      (srcFn := fun a b p => Data.LLVM.Int.mul a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .mul))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hxType hcType
  subst hCf
  -- Pin the constant operand to `2`.
  have hcConstVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hcType
  obtain rfl : cv = Data.LLVM.Int.constant intType.bitwidth intAttr.value := by
    have := hcVal.symm.trans hcConstVal; simpa using this
  have hDomX : x.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hxIn : x.InBounds ctx.raw := by grind
  have xNotOp : ¬ x ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the single `llvm.add` creation.
  peelOpCreation! hpattern ctx₁ addOp hAdd hDomX hDomX₁
  cleanupHpattern hpattern
  -- Structural facts about the created `add`.
  have hAddType : addOp.getOpType! ctx₁.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAdd (operation := addOp)]
  have hAddOperands : addOp.getOperands! ctx₁.raw = #[x, x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAdd (operation := addOp)]
  have hAddResTypes : addOp.getResultTypes! ctx₁.raw
      = #[⟨Attribute.integerType intType, by grind⟩] := by
    have := OperationPtr.getResultTypes!_WfRewriter_createOp hAdd (operation := addOp)
    grind [Subtype.ext]
  have hAddProps : addOp.getProperties! ctx₁.raw (.llvm .add)
      = op.getProperties! ctx.raw (.llvm .mul) := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAdd (operation := addOp)]
  -- Read the refined operand in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₁ xNotOp
  -- Replay the created `add` forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.add a b
        (op.getProperties! ctx.raw (.llvm .mul)).nsw (op.getProperties! ctx.raw (.llvm .mul)).nuw)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddType hAddProps hAddOperands hAddResTypes hXVal' hXVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int intType.bitwidth (Data.LLVM.Int.add xt xt
      (op.getProperties! ctx.raw (.llvm .mul)).nsw
      (op.getProperties! ctx.raw (.llvm .mul)).nuw)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  rw [hVal2]
  exact isRefinedBy_trans
    (by simpa using Data.LLVM.Int.mulo_by_2_unsigned_signed hWidth (x := xv))
    (Data.LLVM.Int.add_mono xv xv xt xt hxRef hxRef _ _)

/-! ### trunc_of_zext

  `trunc (zext x) -> x` when the truncation lands back on `x`'s type. A two-level DAG match:
  the `zext` is reached through the `trunc`'s defining op, so its runtime value comes from
  `zext_getVar?_of_EquationLemmaAt`. There is no `Verified.llvm_trunc` bundle, but the
  pattern's own type guards supply every type fact the proof needs.
-/

/-- Narrowing-unary analogue of `matchExtOp_interpretOp_unfold`, for `llvm.trunc` on an
    integer operand: reads the operand's `i{opType}` value and binds the result to
    `Data.LLVM.Int.trunc`. (`matchExtOp_interpretOp_unfold` only covers *widening* casts,
    where `srcFn` takes `w₁ < w₂`.) -/
private theorem matchTruncOp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {operand : ValuePtr} {props : propertiesOf (.llvm .trunc)}
    {opType resType : IntegerType} {hIsTy}
    {state : InterpreterState ctx} {newState cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .trunc)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hProps : props = op.getProperties! ctx.raw (.llvm .trunc))
    (hResTypes : op.getResultTypes! ctx.raw = #[⟨.integerType resType, hIsTy⟩])
    (hw : resType.bitwidth < opType.bitwidth)
    (hSemSrc : ∀ (w₁ : Nat) (resTy : IntegerType) (hw : resTy.bitwidth < w₁)
        (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm .trunc)) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' .trunc props #[⟨.integerType resTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
          = some (.ok (#[.int resTy.bitwidth
              (Data.LLVM.Int.trunc x resTy.bitwidth props.nsw props.nuw hw)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hOperandType : (operand.getType! ctx.raw).val = Attribute.integerType opType) :
    ∃ xv, state.variables.getVar? operand = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int resType.bitwidth
          (Data.LLVM.Int.trunc xv resType.bitwidth props.nsw props.nuw hw)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : operand = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨val, hval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hgetVar : state.variables.getVar? operand = some val := by
    rw [hOperandEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hval
  have hconf := VariableState.getVar?_conforms hgetVar
  rw [show operand.getType! ctx.raw
        = ⟨.integerType opType, hOperandType ▸ (operand.getType! ctx.raw).2⟩
      from Subtype.ext hOperandType] at hconf
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType hconf
  refine ⟨xv, hgetVar, ?_⟩
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int opType.bitwidth xv] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    obtain rfl : i = 0 := by omega
    simpa [hOperand0] using hgetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp'] at hInterp'
  rw [hResTypes] at hInterp'
  rw [hSemSrc _ _ hw] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.int resType.bitwidth
      (Data.LLVM.Int.trunc xv resType.bitwidth props.nsw props.nuw hw)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

set_option maxHeartbeats 1000000 in
theorem trunc_of_zext_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps trunc_of_zext_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges trunc_of_zext_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds trunc_of_zext_local}
    {h₄ : LocalRewritePattern.ReturnValues trunc_of_zext_local} :
    LocalRewritePattern.PreservesSemantics trunc_of_zext_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, trunc_of_zext_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchTrunc`.
  have hMatchSome : (matchTrunc op ctx.raw).isSome := by
    cases hM : matchTrunc op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, tProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchTrunc_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the defining `zext`.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨zextOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hZextSome : (matchZext zextOp ctx.raw).isSome := by
    cases hM : matchZext zextOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, zProps⟩, hZext⟩ := Option.isSome_iff_exists.mp hZextSome
  rw [hZext] at hpattern
  simp only [] at hpattern
  -- Guard: the trunc lands back on `x`'s type.
  have hTypeEq : ((op.getResult 0).get! ctx.raw).type = x.getType! ctx.raw := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hTypeEq] at hpattern
  -- Guards: `x : i32` and `v0 : i64`.
  obtain ⟨xt, hxTypeVal⟩ :
      ∃ t, (x.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (x.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hxTypeVal] at hpattern
  simp only [] at hpattern
  obtain ⟨zt, hzTypeVal⟩ :
      ∃ t, (v0.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (v0.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hzTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  -- Destructure the bitwidths so the Layer-0 lemma's literal `32`/`64` widths apply.
  obtain ⟨bwx⟩ := xt
  obtain ⟨bwz⟩ := zt
  simp only at hWidthRaw hxTypeVal hzTypeVal hTypeEq
  obtain ⟨rfl, rfl⟩ : bwx = 32 ∧ bwz = 64 := by omega
  -- The op's single result type, as read by the interpreter.
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val
      = Attribute.integerType ⟨32⟩ := by rw [hTypeEq, hxTypeVal]
  have hResTypes0 : op.getResultTypes! ctx.raw = #[((op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  have hTypeAttrEq : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType ⟨32⟩, hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr) := Subtype.ext hResTypeVal
  have hResTypes : op.getResultTypes! ctx.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hResTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr)] := by
    rw [hResTypes0]; exact congrArg (fun t => #[t]) hTypeAttrEq
  have hw : (IntegerType.mk 32).bitwidth < (IntegerType.mk 64).bitwidth := by decide
  -- Unfold the matched `trunc`'s interpretation.
  obtain ⟨v0v, hv0Val, hMem, hRes, hCf⟩ :=
    matchTruncOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hResTypes
      hw (by intro w₁ resTy hw' xx pp hIsTy bo mem
             simp [Llvm.interpretOp', ge_iff_le, Nat.not_le.mpr hw', pure, Interp])
      hinterp hzTypeVal
  subst hCf
  -- Recover the defining `zext`'s value.
  obtain ⟨opType', hw', xv, hxVal, hv0ZextVal, hxType', hDomX, hxIn, hxNotRes⟩ :=
    zext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hZext
      (by rw [hOperands]; simp) hzTypeVal
  obtain rfl : opType' = ⟨32⟩ := by rw [hxType'] at hxTypeVal; grind
  obtain rfl : v0v = Data.LLVM.Int.zext xv 64 zProps.nneg hw' := by
    have := hv0Val.symm.trans hv0ZextVal; simpa using this
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[x] := by
    simp at hpattern; grind
  obtain ⟨xtv, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX hxNotRes
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int 32 xtv], by simp [hXVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- `trunc (zext x) ⊒ x` at the guarded widths, then transport along `x ⊒ xt`.
  have hLem := Data.LLVM.Int.trunc_of_zext (n := zProps.nneg) (s := tProps.nsw)
    (u := tProps.nuw) (x := xv)
  exact isRefinedBy_trans (by simpa using hLem) hxRef

/-! ### select_to_iminmax

  `(icmp pred X Y) ? X : Y -> {u,s}{max,min} X Y`, eight instances of one shape. The `icmp`
  is reached through the `select`'s condition operand, so its runtime value comes from a
  Layer-3 graph lemma; the emitted intrinsic is replayed with the LLVM forward lemma.
-/

set_option maxHeartbeats 1000000 in
/-- Semantic content of a successful `matchIcmp` on the *defining op* of `cond`, an operand of
    `op`: in a source state satisfying `EquationLemmaAt` before `op`, `cond`'s runtime value is
    `Data.LLVM.Int.icmp xv yv pred`. The `icmp` analogue of
    `matchAdd_getVar?_of_EquationLemmaAt`; the comparison's operand type is supplied by the
    caller (for `select_to_iminmax` it is the `select`'s value type). -/
private theorem matchIcmp_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {cond il ir : ValuePtr} {icmpOp : OperationPtr} {iProps : propertiesOf (.llvm .icmp)}
    {intType : IntegerType}
    (hDef : getDefiningOp cond ctx.raw = some icmpOp)
    (hIcmp : matchIcmp icmpOp ctx.raw = some (il, ir, iProps))
    (hOperand : cond ∈ op.getOperands! ctx.raw)
    (hIlType : (il.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ (xv yv : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? il = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? ir = some (RuntimeValue.int intType.bitwidth yv) ∧
      state.variables.getVar? cond = some (RuntimeValue.int 1
        (Data.LLVM.Int.icmp xv yv iProps.predicate)) := by
  obtain ⟨hIcmpType, hIcmpNumResults, hIcmpOperands, hIcmpProps⟩ := matchIcmp_implies hIcmp
  obtain ⟨condPtr, rfl⟩ : ∃ p, cond = ValuePtr.opResult p := by
    cases cond with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hIcmpOpEq : condPtr.op = icmpOp := by simp [getDefiningOp] at hDef; grind
  subst hIcmpOpEq
  have hCondIn : (ValuePtr.opResult condPtr).InBounds ctx.raw := by grind
  have hIcmpOpIn : condPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : condPtr.index < condPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCondEq : condPtr = condPtr.op.getResult 0 := by
    have hidx : condPtr.index = 0 := by omega
    cases condPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  -- Verifier facts: the two comparison operands share a type.
  have hIcmpVerified : condPtr.op.Verified ctx hIcmpOpIn := by grind
  obtain ⟨-, -, -, -, -, hOperandTypesEq⟩ :=
    OperationPtr.Verified.llvm_icmp hIcmpVerified hIcmpType
  have hilEq : il = (condPtr.op.getOperands! ctx.raw)[0]! := by rw [hIcmpOperands]; rfl
  have hirEq : ir = (condPtr.op.getOperands! ctx.raw)[1]! := by rw [hIcmpOperands]; rfl
  have hIcmpOperand0 : condPtr.op.getOperand! ctx.raw 0 = il := by
    rw [hilEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hIcmpOperand1 : condPtr.op.getOperand! ctx.raw 1 = ir := by
    rw [hirEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hIrType : (ir.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hIcmpOperand1, ← hOperandTypesEq, hIcmpOperand0, hIlType]
  -- Dominance and purity: the `icmp` has already been interpreted into `state`.
  have hIcmpDefines : (ValuePtr.opResult condPtr).getDefiningOp! ctx.raw = some condPtr.op := by
    have hOwner := (ctx.wellFormed.operations condPtr.op hIcmpOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hIcmpSDom : condPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hIcmpDefines hOperand
  have hIcmpDomIp : condPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hIcmpPure : condPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_icmp hIcmpType
  obtain ⟨cfI, hInterpIcmp⟩ := stateWf condPtr.op hIcmpOpIn hIcmpPure hIcmpDomIp
  -- Unfold the `icmp`'s interpretation (`newState := state`).
  obtain ⟨xv, yv, hxVal, hyVal, -, hCondResVal, -⟩ :=
    matchIcmp_interpretOp_unfold hIcmpOpIn hIcmpType hIcmpNumResults hIcmpOperands rfl
      hInterpIcmp hIlType hIrType
  refine ⟨xv, yv, hxVal, hyVal, ?_⟩
  rw [hCondEq, hCondResVal, hIcmpProps]

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the eight `select_to_iminmax` combines. Parameterized over the
    matched predicate `pred`, the emitted intrinsic `dst` with its (unit) properties `dprops`,
    the data-level function `f` that `dst` computes (`hSemDst`), the monotonicity of `f`
    (`hMono`), and the value-refinement lemma (`hRefine`). -/
theorem selectToIMinMaxLocal_preservesSemantics
    {pred : Data.LLVM.IntPred} {dst : Llvm} {dprops : propertiesOf (.llvm dst)}
    {f : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    (hSemDst : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' dst dprops resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok (#[.int bw (f x y)], mem, none)))
    (hMono : ∀ {bw : Nat} (x₁ x₂ y₁ y₂ : Data.LLVM.Int bw), x₁ ⊒ y₁ → x₂ ⊒ y₂ →
        f x₁ x₂ ⊒ f y₁ y₂)
    (hRefine : ∀ {bw : Nat}, (bw = 64 ∨ bw = 32) → ∀ (x y : Data.LLVM.Int bw),
        Data.LLVM.Int.select (Data.LLVM.Int.icmp x y pred) x y ⊒ f x y)
    {h : LocalRewritePattern.ReturnOps (selectToIMinMaxLocal pred dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (selectToIMinMaxLocal pred dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (selectToIMinMaxLocal pred dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (selectToIMinMaxLocal pred dst dprops)} :
    LocalRewritePattern.PreservesSemantics (selectToIMinMaxLocal pred dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectToIMinMaxLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchSelect`.
  have hMatchSome : (matchSelect op ctx.raw).isSome := by
    cases hM : matchSelect op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tv, fv⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  -- Establish this before peeling, while `hpattern` is still small: with the createOp bind and
  -- three equality guards in scope, `grind` blows up (see `ProofStrategy.md`).
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨hNRes, hNOper, ⟨condIt, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvEq : tv = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvEq : fv = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tv := by
    rw [hTvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fv := by
    rw [hFvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Result-type and bitwidth guards.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : intType.bitwidth = 64 ∨ intType.bitwidth = 32 := by omega
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTvType : (tv.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFvType : (fv.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  -- Peel the defining `icmp` and the three equality guards.
  have hDefSome : (getDefiningOp cond ctx.raw).isSome := by
    cases hM : getDefiningOp cond ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨icmpOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hIcmpSome : (matchIcmp icmpOp ctx.raw).isSome := by
    cases hM : matchIcmp icmpOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨il, ir, ip⟩, hIcmp⟩ := Option.isSome_iff_exists.mp hIcmpSome
  rw [hIcmp] at hpattern
  simp only [] at hpattern
  have hPred : ip.predicate = pred := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hPred] at hpattern
  have hIlTv : il = tv := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hIlTv] at hpattern
  have hIrFv : ir = fv := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hIrFv] at hpattern
  -- Unfold the matched `select`'s interpretation.
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTvType hFvType hinterp
  subst hCf
  -- Recover the condition's value from the defining `icmp`.
  obtain ⟨xv, yv, hxVal, hyVal, hCondVal⟩ :=
    matchIcmp_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hIcmp
      (by rw [hOperands]; simp) (by rw [hIlTv]; exact hTvType)
  obtain rfl : xv = tvv := by
    have := (hIlTv ▸ hxVal).symm.trans htVal; simpa using this
  obtain rfl : yv = fvv := by
    have := (hIrFv ▸ hyVal).symm.trans hfVal; simpa using this
  obtain rfl : cv = Data.LLVM.Int.icmp xv yv ip.predicate := by
    have := hcVal.symm.trans hCondVal; simpa using this
  -- Dominance / freshness for the two value operands.
  have hDomT : tv.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomF : fv.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hTIn : tv.InBounds ctx.raw := by grind
  have hFIn : fv.InBounds ctx.raw := by grind
  have tNotOp : ¬ tv ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have fNotOp : ¬ fv ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the single intrinsic creation.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomT hDomT₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[tv, fv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hOpResTypeAttr : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := Subtype.ext hResType
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResTypeAttr
  have hDomF₁ : fv.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind) (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomF
  -- Read both refined operands in the target state.
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTIn htVal
      hDomT hDomT₁ tNotOp
  obtain ⟨ft, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFIn hfVal
      hDomF hDomF₁ fNotOp
  -- Replay the created intrinsic forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => f a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hNewType hNewProps hNewOperands hNewResTypes hTVal' hFVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int intType.bitwidth (f tt ft)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  rw [hPred]
  exact isRefinedBy_trans (by simpa using hRefine hWidth xv yv) (hMono xv yv tt ft htRef hfRef)

/-! The eight instantiations. -/

theorem select_to_iminmax_ugt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .ugt .intr__umax ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.umax a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_ugt hw)

theorem select_to_iminmax_uge_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .uge .intr__umax ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.umax a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_uge hw)

theorem select_to_iminmax_sgt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .sgt .intr__smax ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.smax a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_sgt hw)

theorem select_to_iminmax_sge_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .sge .intr__smax ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.smax a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_sge hw)

theorem select_to_iminmax_ult_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .ult .intr__umin ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.umin a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_ult hw)

theorem select_to_iminmax_ule_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .ule .intr__umin ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.umin a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_ule hw)

theorem select_to_iminmax_slt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .slt .intr__smin ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.smin a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_slt hw)

theorem select_to_iminmax_sle_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (selectToIMinMaxLocal .sle .intr__smin ()) h h₂ h₃ h₄ :=
  selectToIMinMaxLocal_preservesSemantics (f := fun a b => Data.LLVM.Int.smin a b)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw x y => Data.LLVM.Int.select_to_iminmax_sle hw)

end Veir.RISCV
