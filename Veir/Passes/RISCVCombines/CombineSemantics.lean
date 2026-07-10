import Veir.Passes.RISCVCombines.Combine
import Veir.Passes.RISCVCombines.LLVMProofs
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
import Veir.Passes.InstructionSelection.RewriteProofs.LowerExt
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBexti
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSlti
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRotate
import Veir.Passes.RISCVCombines.Proofs

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

  * The six `not_cmp_fold` combines, and the two `match_selects`
    combines create one operation, and so additionally have to replay that operation forward in
    the target state. `match_selects` (`select c C1 0 → {zext,sext} c`) emits a *width-changing*
    extension of the `select`'s `i1` condition, replayed with `interpretOp_llvm_unaryInt_forward`.
    `not_cmp_fold` is the op-creating *and* DAG-matching exemplar: `op` is the `xor _, -1`
    (matched with `matchNot` on its own result), its non-constant operand is the result of a
    defining `icmp`, and it emits an `icmp` with the inverted predicate on the *inner*
    comparison's operands — so it fuses `selectToIMinMaxLocal`'s emit-and-replay with the
    graph-lemma recovery of a defining op used by `sub_add_reg`. The two negated `sub_add_reg`
    combines (`x - (y + x) → 0 - y`, `x - (x + y) → 0 - y`) create *two* operations — a fresh
    `llvm.mlir.constant 0` (replayed with `interpretOp_llvm_constant_forward`) and the `sub` — so
    they are the two-op-creating exemplar. The six `redundant_binop_in_equality` combines
    (`(binop X Y) cmp X → Y cmp 0`, `binop ∈ {add,sub,xor}`, `cmp ∈ {eq,ne}`) reuse that two-op
    tail (constant `0` + emitted `icmp`) and recover the defining binop's value with a *generic*
    graph lemma `matchBinop_getVar?_of_EquationLemmaAt` parameterized over the binop opcode. The
    two `double_icmp_zero` combines (`(icmp X 0 pred) outer (icmp Y 0 pred) → icmp (X | Y) 0 pred`,
    `outer ∈ {and, or}`) are the two-branch-DAG-matching exemplar: *both* operands of the outer
    `and`/`or` are recovered through defining `icmp`s (`matchIcmpZero_getVar?_of_EquationLemmaAt`,
    which also pins the compared constant to `0`), and they create *three* ops (`or`, `constant 0`,
    `icmp`). `NotAPlusNegOne` (`not (add X (-1)) → 0 - X`) combines the `matchNot`-on-`op` recovery
    (`op` is the `xor _, -1`) with a defining `add X (-1)`, recovered — constant operand pinned —
    by `matchBinopSndConst_getVar?_of_EquationLemmaAt`, then creates a `constant 0` and a `sub`.

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

/-- Interpreter computation fact for `llvm.trunc` at a singleton integer result-type array. The
    narrowing cousin of `zext_interpretOp'`/`sext_interpretOp'` (`LowerExt.lean`). -/
theorem trunc_interpretOp' (w₁ : Nat) (resTy : IntegerType) (hw : resTy.bitwidth < w₁)
    (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm .trunc)) (hIsTy)
    (blockOperands : Array BlockPtr) (mem : MemoryState) :
    Llvm.interpretOp' .trunc props #[⟨.integerType resTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
      = some (.ok (#[.int resTy.bitwidth
          (Data.LLVM.Int.trunc x resTy.bitwidth props.nsw props.nuw hw)], mem, none)) := by
  simp [Llvm.interpretOp', ge_iff_le, Nat.not_le.mpr hw, pure, Interp]

/-- `llvm.trunc` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_trunc {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .trunc) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- Layer-3 graph lemma for an operand `base` defined by an `llvm.trunc`: in a source state
    satisfying `EquationLemmaAt` before `op`, `base`'s runtime value is `trunc xv`, and the wide
    value `x`'s facts are recovered. The narrowing analogue of `zext_getVar?_of_EquationLemmaAt`
    (`LowerExt.lean`).

    `base`'s type being an integer is what selects the integer arm of `IsVerifiedTruncop` — the
    `llvm.trunc` verifier also admits `byte`-typed operands, and that arm never arises here. -/
theorem trunc_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x : ValuePtr} {truncOp : OperationPtr} {tProps : propertiesOf (.llvm .trunc)}
    {retType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some truncOp)
    (hTrunc : matchTrunc truncOp ctx.raw = some (x, tProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType retType) :
    ∃ (opType : IntegerType) (hw : retType.bitwidth < opType.bitwidth)
      (xv : Data.LLVM.Int opType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int retType.bitwidth
        (Data.LLVM.Int.trunc xv retType.bitwidth tProps.nsw tProps.nuw hw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType opType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hTruncType, hTruncNumResults, hTruncOperands, hTProps⟩ := matchTrunc_implies hTrunc
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hTruncOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hTruncVerified : basePtr.op.Verified ctx hTruncOpIn := by grind
  -- `base`'s type is the `trunc`'s result type, so the verifier's integer arm applies.
  have hVTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hbaseEq]; rfl
  have hResTypeVal : ((basePtr.op.getResult 0).get! ctx.raw).type.val
      = Attribute.integerType retType := by rw [← hVTypeEq]; exact hBaseType
  obtain ⟨-, -, -, -, hInt⟩ := OperationPtr.Verified.llvm_trunc hTruncVerified hTruncType
  obtain ⟨opType, hxTypeV, hwV⟩ := hInt retType hResTypeVal
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hTruncOperands]; rfl
  have hTruncOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType opType := by
    rw [← hTruncOperand0]; exact hxTypeV
  have hResTypes0 : basePtr.op.getResultTypes! ctx.raw
      = #[((basePtr.op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hTruncNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hTruncNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := basePtr.op) (ctx := ctx.raw)
        (index := 0) (by omega)
      grind
  have hResTypes : basePtr.op.getResultTypes! ctx.raw
      = #[⟨Attribute.integerType retType,
          hResTypeVal ▸ ((basePtr.op.getResult 0).get! ctx.raw).type.2⟩] :=
    hResTypes0.trans (congrArg (fun t => #[t]) (Subtype.ext hResTypeVal))
  -- Dominance, purity, and the `EquationLemmaAt` interpretation of the `trunc`.
  have hTruncDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hTruncOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hTruncSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hTruncDefines
      hOperand
  have hTruncDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hTruncPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_trunc hTruncType
  obtain ⟨cfT, hInterpTrunc⟩ := stateWf basePtr.op hTruncOpIn hTruncPure hTruncDomIp
  obtain ⟨xv, hxVal, -, hBaseResVal, -⟩ :=
    matchTruncOp_interpretOp_unfold (props := basePtr.op.getProperties! ctx.raw (.llvm .trunc))
      hTruncOpIn hTruncType hTruncNumResults hTruncOperands rfl hResTypes hwV
      (fun w₁ resTy hw' xx pp hIsTy bo mem => trunc_interpretOp' w₁ resTy hw' xx pp hIsTy bo mem)
      hInterpTrunc hxType
  refine ⟨opType, hwV, xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hbaseEq, hBaseResVal, ← hTProps]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hTruncOpIn (by grind [OperationPtr.getOperands!])) hTruncSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hTruncSDom) x
      (by grind [OperationPtr.getOperands!])

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

/-! ### not_cmp_fold

  `(icmp pred X Y) ^ -1 → (icmp invPred X Y)`. `op` is the `xor _, -1`, matched with `matchNot`
  on its own result; its non-constant operand is the result of a defining `icmp`. So the proof
  is a *two-level* DAG match — the `icmp` reached through `op`'s operand, and its runtime value
  recovered from `EquationLemmaAt` — plus the constant `-1` operand pinned to its value. The
  emitted `icmp X Y invPred` reuses the *inner* `icmp`'s operands `X`/`Y`, so the graph lemma
  additionally exposes their target-side facts (dominance, in-bounds, not-a-result-of-`op`), like
  `matchAdd_getVar?_of_EquationLemmaAt`.
-/

set_option maxHeartbeats 1000000 in
/-- Semantic content of a successful `matchIcmp` on the *defining op* of an operand `cond` of `op`,
    exposing the comparison operands `il`/`ir` together with everything a `PreservesSemantics`
    proof that re-emits on them needs. The richer cousin of the `private`
    `matchIcmp_getVar?_of_EquationLemmaAt` above (which returns only values, for `select_to_iminmax`
    which re-emits on the `select`'s own operands); modelled on
    `matchAdd_getVar?_of_EquationLemmaAt`. -/
private theorem notCmpFold_icmp_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
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
        (Data.LLVM.Int.icmp xv yv iProps.predicate)) ∧
      (il.getType! ctx.raw).val = Attribute.integerType intType ∧
      (ir.getType! ctx.raw).val = Attribute.integerType intType ∧
      il.dominatesIp (InsertPoint.before op) ctx ∧
      ir.dominatesIp (InsertPoint.before op) ctx ∧
      il.InBounds ctx.raw ∧ ir.InBounds ctx.raw ∧
      il ∉ op.getResults! ctx.raw ∧ ir ∉ op.getResults! ctx.raw := by
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
  refine ⟨xv, yv, hxVal, hyVal, ?_, hIlType, hIrType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCondEq, hCondResVal, hIcmpProps]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hIcmpOpIn (by grind [OperationPtr.getOperands!])) hIcmpSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hIcmpOpIn (by grind [OperationPtr.getOperands!])) hIcmpSDom
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hIcmpSDom) il
      (by grind [OperationPtr.getOperands!])
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hIcmpSDom) ir
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the six `not_cmp_fold` combines. Parameterized over the matched
    predicate `pred` and the emitted inverted predicate `invPred`, with the data-level obligation
    supplied as `hRefine` (`xor (icmp x y pred) (-1) ⊒ icmp x y invPred`). -/
theorem notCmpFoldLocal_preservesSemantics
    {pred invPred : Data.LLVM.IntPred}
    (hRefine : ∀ {w : Nat}, (w = 64 ∨ w = 32) → ∀ (x y : Data.LLVM.Int w),
        Data.LLVM.Int.xor (Data.LLVM.Int.icmp x y pred) (Data.LLVM.Int.constant 1 (-1))
          ⊒ Data.LLVM.Int.icmp x y invPred)
    {h : LocalRewritePattern.ReturnOps (notCmpFoldLocal pred invPred)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (notCmpFoldLocal pred invPred)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (notCmpFoldLocal pred invPred)}
    {h₄ : LocalRewritePattern.ReturnValues (notCmpFoldLocal pred invPred)} :
    LocalRewritePattern.PreservesSemantics (notCmpFoldLocal pred invPred) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, notCmpFoldLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchNot (op.getResult 0)`: `op` is the `xor _, -1`.
  have hNotSome : (matchNot (op.getResult 0) ctx.raw).isSome := by
    cases hM : matchNot (op.getResult 0) ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨icmpV, hNot⟩ := Option.isSome_iff_exists.mp hNotSome
  -- `matchNot`'s structure: `op` is an `xor icmpV rhs`, `rhs` a `-1` constant.
  obtain ⟨opResultPtr, rhs, cst, hResEq, hXori, hCstMatch, hCstVal⟩ := matchNot_implies hNot
  have hOpEq : opResultPtr.op = op := by
    have : (ValuePtr.opResult (op.getResult 0)) = ValuePtr.opResult opResultPtr := hResEq
    simp only [OperationPtr.getResult, ValuePtr.opResult.injEq] at this
    grind
  rw [hOpEq] at hXori
  obtain ⟨hXorType, hXorNumResults, hXorOperands⟩ := matchXori_implies hXori
  -- Establish `op`'s single result equation now, while `hpattern` is small.
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hNot] at hpattern
  simp only [] at hpattern
  -- Peel the defining `icmp` and predicate guard.
  have hDefSome : (getDefiningOp icmpV ctx.raw).isSome := by
    cases hM : getDefiningOp icmpV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨icmpOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hIcmpSome : (matchIcmp icmpOp ctx.raw).isSome := by
    cases hM : matchIcmp icmpOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y, ip⟩, hIcmp⟩ := Option.isSome_iff_exists.mp hIcmpSome
  rw [hIcmp] at hpattern
  simp only [] at hpattern
  have hPred : ip.predicate = pred := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hPred] at hpattern
  -- The comparison-operand type/bitwidth guard.
  obtain ⟨cmpType, hCmpType⟩ :
      ∃ cmpType, (x.getType! ctx.raw).val = Attribute.integerType cmpType := by
    cases hr : (x.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hCmpType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : cmpType.bitwidth = 64 ∨ cmpType.bitwidth = 32 := by omega
  -- Verifier facts for `op` (the `xor`): both operands and the result share `xorType` (`i1`).
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, xorType, hXorResType, hXorOperand0Type, hXorOperand1Type⟩ :=
    OperationPtr.Verified.llvm_xor opVerif hXorType
  have hIcmpVEq : icmpV = (op.getOperands! ctx.raw)[0]! := by rw [hXorOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hXorOperands]; rfl
  have hXorOperand0 : op.getOperand! ctx.raw 0 = icmpV := by
    rw [hIcmpVEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hXorOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hIcmpVType : (icmpV.getType! ctx.raw).val = Attribute.integerType xorType := by
    rw [← hXorOperand0, hXorOperand0Type]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType xorType := by
    rw [← hXorOperand1, hXorOperand1Type]
  -- Unfold the matched `xor`'s interpretation: its result is `xor icmpVal rhsVal`.
  obtain ⟨icmpVal, rhsVal, hicmpVal, hrhsVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .xor)
      (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
      (props := op.getProperties! ctx.raw (.llvm .xor))
      opInBounds hXorType hXorNumResults hXorOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hIcmpVType hRhsType
  subst hCf
  -- Recover the defining `icmp`'s value and its operands' target-side facts.
  have hIcmpVMem : icmpV ∈ op.getOperands! ctx.raw := by rw [hXorOperands]; simp
  obtain ⟨xv, yv, hxVal, hyVal, hCondVal, hxType, hyType, hDomX, hDomY, hxIn, hyIn,
      xNotOp, yNotOp⟩ :=
    notCmpFold_icmp_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hIcmp
      hIcmpVMem hCmpType
  -- The two reads of `icmpV`'s value agree, forcing `xorType` to be `i1`.
  have hXorBw0 : xorType.bitwidth = 1 := by
    have := hicmpVal.symm.trans hCondVal
    simp only [Option.some.injEq, RuntimeValue.int.injEq] at this
    exact this.1
  -- Collapse `xorType` to the literal `i1`, so the `xor`/`icmp` values live at width 1.
  obtain ⟨xorW⟩ := xorType; simp only at hXorBw0; subst hXorBw0
  obtain rfl : icmpVal = Data.LLVM.Int.icmp xv yv ip.predicate := by
    have := hicmpVal.symm.trans hCondVal; simpa using this
  -- Pin the constant operand `rhs` to `-1`.
  have hrhsConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hXorOperands]; simp) hRhsType
  obtain rfl : rhsVal = Data.LLVM.Int.constant 1 cst.value := by
    have := hrhsVal.symm.trans hrhsConst; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Dominance / in-bounds for the emitted `icmp`'s operands in the created context.
  have hDomT : x.dominatesIp (InsertPoint.before op) ctx := hDomX
  have hDomF : y.dominatesIp (InsertPoint.before op) ctx := hDomY
  -- Peel the single `icmp` creation.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomT hDomT₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm .icmp := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.llvm .icmp) = IcmpProperties.mk invPred := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  -- The created `icmp`'s result type is `op`'s result type, which is `i1` (= `xorType`).
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hXorResType
  have hDomF₁ : y.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomF
  -- Read both refined operands in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomT₁ xNotOp
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomF₁ yNotOp
  -- Replay the created `icmp` forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_icmp_forward (state := state') (inBounds := by grind)
      (i1t := ⟨1⟩) (f := fun a b => Data.LLVM.Int.icmp a b invPred) rfl
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNewType hNewProps hNewOperands hNewResTypes hXVal' hYVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 1 (Data.LLVM.Int.icmp xt yt invPred)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: source value `xor (icmp xv yv pred) (-1)` refines `icmp xt yt invPred`.
  simp only [Data.LLVM.Int.cast_self]
  rw [hPred, hCstVal]
  refine isRefinedBy_trans (hRefine hWidth xv yv)
    (Data.LLVM.Int.icmp_mono xv yv xt yt invPred hxRef hyRef)

/-! The six instantiations. -/

theorem not_cmp_fold_eq_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .eq .ne) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_eq hw)

theorem not_cmp_fold_ne_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .ne .eq) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_ne hw)

theorem not_cmp_fold_ugt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .ugt .ule) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_ugt hw)

theorem not_cmp_fold_uge_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .uge .ult) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_uge hw)

theorem not_cmp_fold_sgt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .sgt .sle) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_sgt hw)

theorem not_cmp_fold_sge_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (notCmpFoldLocal .sge .slt) h h₂ h₃ h₄ :=
  notCmpFoldLocal_preservesSemantics (fun hw _ _ => Data.LLVM.Int.not_cmp_fold_sge hw)

/-! ### match_selects

  `select c C1 0 → ext c`, with `(C1, ext) ∈ {(1, zext), (-1, sext)}`. The condition `c` is an
  operand of the `select`, so — unlike `not_cmp_fold` — the emitted op's operand needs no graph
  lemma; its facts come straight from `Dom.operand_dominates_op`. The two dropped arms are
  constants, whose runtime values are pinned to `C1`/`0` with `matchConstantIntVal`. The emitted
  extension changes width (`i1 → i{w}`), replayed with `interpretOp_llvm_unaryInt_forward`.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the two `match_selects` combines. Parameterized over the required
    true-arm constant `tvVal`, the emitted extension `dst` with its properties `dprops`, the
    width-changing data-level function `f` (`hSemDst`), its monotonicity (`hMono`), and the
    value-refinement lemma (`hRefine`). -/
theorem matchSelectExtLocal_preservesSemantics
    {tvVal : Int} {dst : Llvm} {dprops : propertiesOf (.llvm dst)}
    {f : ∀ {w : Nat}, (1 < w) → Data.LLVM.Int 1 → Data.LLVM.Int w}
    (hSemDst : ∀ (rt : IntegerType) (hw : 1 < rt.bitwidth) (c : Data.LLVM.Int 1) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' dst dprops #[⟨.integerType rt, hIsTy⟩] #[.int 1 c] blockOperands mem
          = some (.ok (#[.int rt.bitwidth (f hw c)], mem, none)))
    (hMono : ∀ {w : Nat} (hlt : 1 < w) (c₁ c₂ : Data.LLVM.Int 1), c₁ ⊒ c₂ → f hlt c₁ ⊒ f hlt c₂)
    (hRefine : ∀ {w : Nat} (_hw : w = 64 ∨ w = 32) (hlt : 1 < w) (c : Data.LLVM.Int 1),
        Data.LLVM.Int.select c (Data.LLVM.Int.constant w tvVal) (Data.LLVM.Int.constant w 0)
          ⊒ f hlt c)
    {h : LocalRewritePattern.ReturnOps (matchSelectExtLocal tvVal dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (matchSelectExtLocal tvVal dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (matchSelectExtLocal tvVal dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (matchSelectExtLocal tvVal dst dprops)} :
    LocalRewritePattern.PreservesSemantics (matchSelectExtLocal tvVal dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, matchSelectExtLocal]
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
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  -- Establish `op`'s single result equation now, while `hpattern` is small.
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨hNRes, hNOper, ⟨condIt, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
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
  have hLt : 1 < intType.bitwidth := by omega
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTvType : (tval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFvType : (fval.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, ← hResEqF, hResType]
  -- Peel the two constant matches and their value guards.
  have hCtSome : (matchConstantIntVal tval ctx.raw).isSome := by
    cases hM : matchConstantIntVal tval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨ctAttr, hCtMatch⟩ := Option.isSome_iff_exists.mp hCtSome
  rw [hCtMatch] at hpattern
  simp only [] at hpattern
  have hCtVal : ctAttr.value = tvVal := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCtVal] at hpattern
  have hCfSome : (matchConstantIntVal fval ctx.raw).isSome := by
    cases hM : matchConstantIntVal fval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cfAttr, hCfMatch⟩ := Option.isSome_iff_exists.mp hCfSome
  rw [hCfMatch] at hpattern
  simp only [] at hpattern
  have hCfVal : cfAttr.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCfVal] at hpattern
  -- Unfold the matched `select`'s interpretation.
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTvType hFvType hinterp
  subst hCf
  -- Pin the two constant arms.
  have htConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCtMatch (by rw [hOperands]; simp) hTvType
  obtain rfl : tvv = Data.LLVM.Int.constant intType.bitwidth ctAttr.value := by
    have := htVal.symm.trans htConst; simpa using this
  have hfConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCfMatch (by rw [hOperands]; simp) hFvType
  obtain rfl : fvv = Data.LLVM.Int.constant intType.bitwidth cfAttr.value := by
    have := hfVal.symm.trans hfConst; simpa using this
  -- Dominance / freshness for the condition operand.
  have hDomC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hCIn : cond.InBounds ctx.raw := by grind
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the single extension creation.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomC hDomC₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[cond] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType intType, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) (Subtype.ext hResType)
  -- Read the refined condition value in the target state.
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
      hDomC hDomC₁ cNotOp
  -- Replay the created extension forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := state') (inBounds := by grind)
      (srcType := ⟨1⟩) (resType := intType) (f := fun c => f hLt c)
      (by intro blockOperands mem; exact hSemDst intType hLt ct _ blockOperands mem)
      hNewType hNewProps hNewOperands hNewResTypes hCVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int intType.bitwidth (f hLt ct)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `select cv (constant tvVal) (constant 0) ⊒ f ct`.
  simp only [Data.LLVM.Int.cast_self]
  rw [hCtVal, hCfVal]
  exact isRefinedBy_trans (hRefine hWidth hLt cv) (hMono hLt cv ct hcRef)

theorem select_1_0_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (matchSelectExtLocal 1 .zext { nneg := false }) h h₂ h₃ h₄ :=
  matchSelectExtLocal_preservesSemantics
    (f := fun {w} hlt c => Data.LLVM.Int.zext c w false hlt)
    (fun rt hw c hIsTy bo mem => zext_interpretOp' 1 rt hw c { nneg := false } hIsTy bo mem)
    (fun hlt c₁ c₂ h => Data.LLVM.Int.zext_mono c₁ c₂ hlt h)
    (fun hw hlt _c => Data.LLVM.Int.select_1_0 hw hlt)

theorem select_neg1_0_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (matchSelectExtLocal (-1) .sext ()) h h₂ h₃ h₄ :=
  matchSelectExtLocal_preservesSemantics
    (f := fun {w} hlt c => Data.LLVM.Int.sext c w hlt)
    (fun rt hw c hIsTy bo mem => sext_interpretOp' 1 rt hw c () hIsTy bo mem)
    (fun hlt c₁ c₂ h => Data.LLVM.Int.sext_mono c₁ c₂ hlt h)
    (fun hw hlt _c => Data.LLVM.Int.select_neg1_0 hw hlt)

/-! ### sub_add_reg (negated forms)

  `x - (y + x) → 0 - y` and `x - (x + y) → 0 - y`. Both match the `add` through the *sub's second
  operand* (`matchAdd_getVar?_of_EquationLemmaAt`), require the matched `x` to be an `add` operand,
  and *create two ops*: a fresh `llvm.mlir.constant 0` and the `sub` computing `0 - y`. So these
  are the two-op-creating exemplar — the tail replays both the constant
  (`interpretOp_llvm_constant_forward`) and the `sub` (`interpretOp_llvm_binaryInt_forward`).
-/

set_option maxHeartbeats 1000000 in
/-- Shared skeleton for the two negated `sub_add_reg` combines: peel `matchSub`, the type/width
    guards and the defining `add` (through `s1`), then expose the `add`'s operand values and the
    matched `sub`'s value `sub s0v (add a0v a1v ..) ..`. -/
private theorem subAddRegNeg_core {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    (ctxVerif : ctx.Verified) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {newState : InterpreterState ctx} {cf} {s0 s1 a0 a1 : ValuePtr} {addOp : OperationPtr}
    {sProps : propertiesOf (.llvm .sub)} {aProps : propertiesOf (.llvm .add)}
    {intType : IntegerType}
    (hMatch : matchSub op ctx.raw = some (s0, s1, sProps))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType)
    (hDef : getDefiningOp s1 ctx.raw = some addOp)
    (hAdd : matchAdd addOp ctx.raw = some (a0, a1, aProps))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (s0v a0v a1v : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? s0 = some (RuntimeValue.int intType.bitwidth s0v) ∧
      state.variables.getVar? a0 = some (RuntimeValue.int intType.bitwidth a0v) ∧
      state.variables.getVar? a1 = some (RuntimeValue.int intType.bitwidth a1v) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.sub s0v (Data.LLVM.Int.add a0v a1v aProps.nsw aProps.nuw)
          sProps.nsw sProps.nuw)) ∧
      cf = none ∧
      a0.dominatesIp (InsertPoint.before op) ctx ∧ a1.dominatesIp (InsertPoint.before op) ctx ∧
      a0.InBounds ctx.raw ∧ a1.InBounds ctx.raw ∧
      a0 ∉ op.getResults! ctx.raw ∧ a1 ∉ op.getResults! ctx.raw := by
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
  -- Recover the defining `add`'s value (through `s1`).
  obtain ⟨a0v, a1v, ha0Val, ha1Val, hs1AddVal, ha0Type, ha1Type, hDom0, hDom1, ha0In, ha1In,
      ha0NotRes, ha1NotRes⟩ :=
    matchAdd_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hAdd
      (by rw [hOperands]; simp) hs1Type
  obtain rfl : s1v = Data.LLVM.Int.add a0v a1v aProps.nsw aProps.nuw := by
    have := hs1Val.symm.trans hs1AddVal; simpa using this
  exact ⟨s0v, a0v, a1v, hs0Val, ha0Val, ha1Val, hMem, by rw [hRes, hProps], hCf,
    hDom0, hDom1, ha0In, ha1In, ha0NotRes, ha1NotRes⟩

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the two negated `sub_add_reg` combines. Parameterized over
    `keepFirst` (which `add` operand is the kept `y`) and the data-refinement lemma `hRefine`,
    which is applied with `s0v` already substituted to the *other* add operand
    (`if keepFirst then a1v else a0v`), so the source is `sub other (add a0v a1v ..) ..`. -/
theorem subAddRegNegLocal_preservesSemantics {keepFirst : Bool}
    (hRefine : ∀ {w : Nat}, (w = 64 ∨ w = 32) → ∀ (a0v a1v : Data.LLVM.Int w)
        (as au ss su : Bool),
        Data.LLVM.Int.sub (if keepFirst then a1v else a0v)
            (Data.LLVM.Int.add a0v a1v as au) ss su
          ⊒ Data.LLVM.Int.sub (Data.LLVM.Int.constant w 0)
              (if keepFirst then a0v else a1v) false false)
    {h : LocalRewritePattern.ReturnOps (subAddRegNegLocal keepFirst)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (subAddRegNegLocal keepFirst)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (subAddRegNegLocal keepFirst)}
    {h₄ : LocalRewritePattern.ReturnValues (subAddRegNegLocal keepFirst)} :
    LocalRewritePattern.PreservesSemantics (subAddRegNegLocal keepFirst) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, subAddRegNegLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchSub`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨s0, s1, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
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
  -- Peel the defining `add` of `s1`.
  have hDefSome : (getDefiningOp s1 ctx.raw).isSome := by
    cases hM : getDefiningOp s1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a0, a1, aProps⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  -- Gather the `add`'s operand values and target-side facts up front.
  obtain ⟨s0v, a0v, a1v, hs0Val, ha0Val, ha1Val, hMem, hRes, hCf, hDom0, hDom1, ha0In, ha1In,
      ha0NotRes, ha1NotRes⟩ :=
    subAddRegNeg_core ctxDom ctxVerif opInBounds stateWf hMatch hResType hDef hAdd hinterp
  subst hCf
  -- Name the kept operand `y`/`yv` and the *other* operand, then resolve them and the guard by
  -- casing on `keepFirst` — collapsing every `if keepFirst` in `hpattern` and the facts to
  -- concrete `a0`/`a1` so the shared tail runs without a `keepFirst`-dependent term.
  obtain ⟨y, yv, hyVal, hDomY, hyIn, hyNotRes, hs0vEq, hyvEq, hpattern⟩ :
      ∃ (y : ValuePtr) (yv : Data.LLVM.Int intType.bitwidth),
        state.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yv) ∧
        y.dominatesIp (InsertPoint.before op) ctx ∧ y.InBounds ctx.raw ∧
        y ∉ op.getResults! ctx.raw ∧
        s0v = (if keepFirst then a1v else a0v) ∧
        yv = (if keepFirst then a0v else a1v) ∧
        ((WfRewriter.createOp! ctx (.llvm .mlir__constant)
            #[(op.getResult 0 : ValuePtr).getType! ctx.raw] #[] #[] #[]
            (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 intType))) none).bind
          (fun x => (WfRewriter.createOp! x.1 (.llvm .sub)
              #[(op.getResult 0 : ValuePtr).getType! x.1.raw] #[x.2.getResult 0, y] #[] #[]
              { nsw := false, nuw := false } none).bind
            (fun x_1 => some (x_1.1, some (#[x.2, x_1.2], #[ValuePtr.opResult (x_1.2.getResult 0)]))))
          = some (newCtx, some (newOps, newValues))) := by
    cases keepFirst with
    | true =>
      simp only [if_true] at hpattern ⊢
      split at hpattern
      case isFalse => simp at hpattern
      rename_i hOtherEq
      exact ⟨a0, a0v, ha0Val, hDom0, ha0In, ha0NotRes,
        by have := hs0Val.symm.trans (hOtherEq ▸ ha1Val); simpa using this, rfl, hpattern⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at hpattern ⊢
      split at hpattern
      case isFalse => simp at hpattern
      rename_i hOtherEq
      exact ⟨a1, a1v, ha1Val, hDom1, ha1In, ha1NotRes,
        by have := hs0Val.symm.trans (hOtherEq ▸ ha0Val); simpa using this, rfl, hpattern⟩
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the two creations: the constant, then the `sub`.
  peelOpCreation! hpattern ctx₁ c0Op hC0 hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ subOp hSub hDomY₁ hDomY₂
  cleanupHpattern hpattern
  -- Structural facts.
  have hC0Type : c0Op.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := c0Op)]
  have hC0Operands : c0Op.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := c0Op)]
  have hC0NeSub : c0Op ≠ subOp := by clear hpattern; grind
  have hC0Props : (c0Op.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨0, intType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC0 (operation := c0Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSub hC0NeSub, h1]
  have hOpResTypeAttr : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := Subtype.ext hResType
  have hGetTypeEq : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact hOpResTypeAttr
  have hGetTypeEq₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [← hGetTypeEq]
    grind [ValuePtr.getType!_WfRewriter_createOp hC0
      (value := ValuePtr.opResult (op.getResult 0))]
  have hC0ResTypes : c0Op.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := c0Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := c0Op)
    rw [if_neg (by clear hpattern; grind)] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hGetTypeEq
  have hSubType : subOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubOperands : subOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (c0Op.getResult 0), y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubProps : subOp.getProperties! ctx₂.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubResTypes : subOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType intType,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := subOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hGetTypeEq₁
  -- Read the refined `y` in the target state.
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ hyNotRes
  -- Replay the constant, then the `sub`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC0Type hC0Props hC0Operands hC0ResTypes
  have hYVal₁ : s₁.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yt) := by
    rw [hFrame₁ y (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hyIn
      (WfRewriter.createOp_new_not_inBounds c0Op hC0))]
    exact hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.sub a b false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubType hSubProps hSubOperands hSubResTypes hRes₁ hYVal₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int intType.bitwidth
      (Data.LLVM.Int.sub (Data.LLVM.Int.constant intType.bitwidth 0) yt false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `sub s0v (add a0v a1v ..) .. ⊒ sub (constant 0) yv .. ⊒ sub (constant 0) yt ..`.
  -- Substitute `s0v` to the *other* add operand, matching `hRefine`'s shape.
  simp only [Data.LLVM.Int.cast_self]
  rw [hs0vEq]
  refine isRefinedBy_trans (hRefine hWidth a0v a1v _ _ _ _)
    (Data.LLVM.Int.sub_mono _ _ _ _ (isRefinedBy_refl _) (hyvEq ▸ hyRef) false false)

theorem sub_add_reg_x_sub_y_add_x_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics (subAddRegNegLocal true) h h₂ h₃ h₄ :=
  subAddRegNegLocal_preservesSemantics
    (fun hw a0v a1v as au ss su => by
      simpa using Data.LLVM.Int.sub_add_reg_x_sub_y_add_x (x := a1v) (y := a0v) hw)

theorem sub_add_reg_x_sub_x_add_y_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics (subAddRegNegLocal false) h h₂ h₃ h₄ :=
  subAddRegNegLocal_preservesSemantics
    (fun hw a0v a1v as au ss su => by
      simpa using Data.LLVM.Int.sub_add_reg_x_sub_x_add_y (x := a0v) (y := a1v) hw)

/-! ### add_shift : `A + shl(0 - B, C) → A - shl(B, C)`

  A three-level DAG match: `op` is the `add`; one of its operands is a defining `shl`; that `shl`'s
  first operand is a defining `sub`; that `sub`'s first operand is a defining `llvm.mlir.constant 0`.
  `shlNegChain` walks the `shl → sub → constant` chain (below the `add`), recovering `B`/`C`'s runtime
  values and target-side facts and pinning `shlNeg`'s value to `shl (sub (constant 0) B) C`. The
  two `add_shift` / `add_shift_commute` proofs then unfold the `add` and re-emit `sub A (shl B C)`.
-/

set_option maxHeartbeats 1000000 in
/-- The `shl (sub (constant 0) B) C` chain below the `add` in `add_shift`: `shlNeg` (an operand of
    `op`, of type `i64`) is defined by a `shl` whose operand 0 is a defining `sub` whose operand 0 is
    a defining `constant 0`. In a source state satisfying `EquationLemmaAt` before `op`, recover the
    runtime values `bv`/`cv` of `B`/`C` (with their dominance/in-bounds/not-a-result facts, since they
    are re-emitted) and pin `shlNeg`'s value to `shl (sub (constant 0) bv) cv`. -/
private theorem shlNegChain {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {shlNeg negB c b zeroV : ValuePtr} {dShl dSub : OperationPtr}
    {shProps : propertiesOf (.llvm .shl)} {subProps : propertiesOf (.llvm .sub)}
    {zc : IntegerAttr}
    (hShlNegMem : shlNeg ∈ op.getOperands! ctx.raw)
    (hShlNegType : (shlNeg.getType! ctx.raw).val = Attribute.integerType ⟨64⟩)
    (hDefShl : getDefiningOp shlNeg ctx.raw = some dShl)
    (hShl : matchShl dShl ctx.raw = some (negB, c, shProps))
    (hCType : (c.getType! ctx.raw).val = Attribute.integerType ⟨64⟩)
    (hDefSub : getDefiningOp negB ctx.raw = some dSub)
    (hSub : matchSub dSub ctx.raw = some (zeroV, b, subProps))
    (hZC : matchConstantIntVal zeroV ctx.raw = some zc)
    (hZCval : zc.value = 0) :
    ∃ (bv cv : Data.LLVM.Int 64),
      state.variables.getVar? b = some (RuntimeValue.int 64 bv) ∧
      state.variables.getVar? c = some (RuntimeValue.int 64 cv) ∧
      state.variables.getVar? shlNeg = some (RuntimeValue.int 64
        (Data.LLVM.Int.shl
          (Data.LLVM.Int.sub (Data.LLVM.Int.constant 64 0) bv subProps.nsw subProps.nuw)
          cv shProps.nsw shProps.nuw)) ∧
      (b.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ ∧
      b.dominatesIp (InsertPoint.before op) ctx ∧ c.dominatesIp (InsertPoint.before op) ctx ∧
      b.InBounds ctx.raw ∧ c.InBounds ctx.raw ∧
      b ∉ op.getResults! ctx.raw ∧ c ∉ op.getResults! ctx.raw := by
  -- ===== shl level =====
  obtain ⟨shlNegPtr, rfl, rfl⟩ := getDefiningOp_implies hDefShl
  obtain ⟨hShlType, hShlNumResults, hShlOperands, hShProps⟩ := matchShl_implies hShl
  have hShlNegIn : (ValuePtr.opResult shlNegPtr).InBounds ctx.raw := by grind
  have hShlOpIn : shlNegPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hShlIdx : shlNegPtr.index < shlNegPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hShlNegEq : shlNegPtr = shlNegPtr.op.getResult 0 := by
    have hidx : shlNegPtr.index = 0 := by omega
    cases shlNegPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hShlVerified : shlNegPtr.op.Verified ctx hShlOpIn := by grind
  obtain ⟨-, -, hShlResEqOp0, ct2, hShlOp1Type⟩ :=
    OperationPtr.Verified.llvm_shl hShlVerified hShlType
  have hVTypeEq : (ValuePtr.opResult shlNegPtr).getType! ctx.raw
      = ((shlNegPtr.op.getResult 0).get! ctx.raw).type := by rw [hShlNegEq]; rfl
  have hnegBIdxEq : negB = (shlNegPtr.op.getOperands! ctx.raw)[0]! := by rw [hShlOperands]; rfl
  have hShlOperand0 : shlNegPtr.op.getOperand! ctx.raw 0 = negB := by
    rw [hnegBIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hnegBType : (negB.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ := by
    have hh : ((shlNegPtr.op.getResult 0).get! ctx.raw).type.val
        = ((shlNegPtr.op.getOperand! ctx.raw 0).getType! ctx.raw).val := hShlResEqOp0
    rw [hShlOperand0] at hh
    rw [← hh, ← hVTypeEq]; exact hShlNegType
  have hShlDefines : (ValuePtr.opResult shlNegPtr).getDefiningOp! ctx.raw = some shlNegPtr.op := by
    have hOwner := (ctx.wellFormed.operations shlNegPtr.op hShlOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShlSDom : shlNegPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hShlDefines hShlNegMem
  have hShlDomIp : shlNegPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShlPure : shlNegPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_shl hShlType
  obtain ⟨cfShl, hInterpShl⟩ := stateWf shlNegPtr.op hShlOpIn hShlPure hShlDomIp
  obtain ⟨negBv, cv, hnegBVal, hcVal, -, hShlResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .shl)
      (srcFn := fun a b p => Data.LLVM.Int.shl a b p.nsw p.nuw)
      (props := shlNegPtr.op.getProperties! ctx.raw (.llvm .shl))
      hShlOpIn hShlType hShlNumResults hShlOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hInterpShl hnegBType hCType
  -- ===== sub level =====
  obtain ⟨subPtr, rfl, rfl⟩ := getDefiningOp_implies hDefSub
  obtain ⟨hSubType, hSubNumResults, hSubOperands, hSubProps⟩ := matchSub_implies hSub
  have hnegBIn : (ValuePtr.opResult subPtr).InBounds ctx.raw := by grind [OperationPtr.getOperands!]
  have hSubOpIn : subPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hSubIdx : subPtr.index < subPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hSubEq : subPtr = subPtr.op.getResult 0 := by
    have hidx : subPtr.index = 0 := by omega
    cases subPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hSubVerified : subPtr.op.Verified ctx hSubOpIn := by grind
  obtain ⟨-, -, -, -, subIntType, hSubResType, hSubOp0Type, hSubOp1Type⟩ :=
    OperationPtr.Verified.llvm_sub hSubVerified hSubType
  have hVTypeEq2 : (ValuePtr.opResult subPtr).getType! ctx.raw
      = ((subPtr.op.getResult 0).get! ctx.raw).type := by rw [hSubEq]; rfl
  -- `negB`'s type is `i64`, so the `sub`'s result and operands are all `i64`.
  have hnegBType2 : ((subPtr.op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨64⟩ := by
    rw [← hVTypeEq2]; exact hnegBType
  have hSubIntType64 : subIntType = ⟨64⟩ := by rw [hSubResType] at hnegBType2; grind
  subst hSubIntType64
  have hzeroVIdxEq : zeroV = (subPtr.op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hbIdxEq : b = (subPtr.op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hSubOperand0 : subPtr.op.getOperand! ctx.raw 0 = zeroV := by
    rw [hzeroVIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hSubOperand1 : subPtr.op.getOperand! ctx.raw 1 = b := by
    rw [hbIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hzeroVType : (zeroV.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ := by
    rw [← hSubOperand0, hSubOp0Type]
  have hbType : (b.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ := by
    rw [← hSubOperand1, hSubOp1Type]
  have hSubDefines : (ValuePtr.opResult subPtr).getDefiningOp! ctx.raw = some subPtr.op := by
    have hOwner := (ctx.wellFormed.operations subPtr.op hSubOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hSubSDomShl : subPtr.op.strictlyDominates shlNegPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hSubDefines
      (by rw [hShlOperands]; simp)
  have hSubSDom : subPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hSubSDomShl hShlSDom
  have hSubDomIp : subPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hSubPure : subPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_sub hSubType
  obtain ⟨cfSub, hInterpSub⟩ := stateWf subPtr.op hSubOpIn hSubPure hSubDomIp
  obtain ⟨zeroVal, bv, hzeroVal, hbVal, -, hSubResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := subPtr.op.getProperties! ctx.raw (.llvm .sub))
      hSubOpIn hSubType hSubNumResults hSubOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hInterpSub hzeroVType hbType
  -- `negB`'s two values agree: `negBv = sub zeroVal bv subProps`.
  rw [← hSubProps] at hSubResVal
  rw [hSubEq] at hnegBVal
  obtain rfl : negBv = Data.LLVM.Int.sub zeroVal bv subProps.nsw subProps.nuw := by
    have hEq := hnegBVal.symm.trans hSubResVal; simpa using hEq
  -- ===== constant level =====
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hZC
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstIn : (ValuePtr.opResult cstPtr).InBounds ctx.raw := by grind [OperationPtr.getOperands!]
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType ⟨64⟩, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    apply Subtype.ext; rw [← heq]; exact hzeroVType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCstSDomSub : cstPtr.op.strictlyDominates subPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hCstDefines
      (by rw [hSubOperands]; simp)
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomSub hSubSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfCst, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType hInterpCst
  -- `zeroVal = constant 64 0`.
  rw [hCstEq] at hzeroVal
  obtain rfl : zeroVal = Data.LLVM.Int.constant 64 zc.value := by
    have hEq := hzeroVal.symm.trans hCstResVal; simpa using hEq
  rw [hZCval] at hShlResVal
  -- Assemble.
  refine ⟨bv, cv, hbVal, hcVal, ?_, hbType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hShlNegEq, hShProps]; exact hShlResVal
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hSubOpIn (by rw [hSubOperands]; simp)) hSubSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShlOpIn (by rw [hShlOperands]; simp)) hShlSDom
  · have hbMem : b ∈ subPtr.op.getOperands! ctx.raw := by rw [hSubOperands]; simp
    grind [OperationPtr.getOperands!]
  · have hcMem : c ∈ shlNegPtr.op.getOperands! ctx.raw := by rw [hShlOperands]; simp
    grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSubSDom) b (by rw [hSubOperands]; simp)
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShlSDom) c (by rw [hShlOperands]; simp)

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `add_shift` / `add_shift_commute`. `commuted` selects which `add`
    operand is the `shl`; the final `cases commuted` applies the matching data lemma
    (`add_shift` / `add_shift_commute`). -/
theorem addShiftLocal_preservesSemantics {commuted : Bool}
    {h : LocalRewritePattern.ReturnOps (addShiftLocal commuted)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (addShiftLocal commuted)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (addShiftLocal commuted)}
    {h₄ : LocalRewritePattern.ReturnValues (addShiftLocal commuted)} :
    LocalRewritePattern.PreservesSemantics (addShiftLocal commuted) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, addShiftLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel matchAdd.
  have hMatchSome : (matchAdd op ctx.raw).isSome := by
    cases hM : matchAdd op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨o0, o1, aProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchAdd_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- `op`'s verifier facts: the two `add` operands share the result type.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, addIntType, hAddResType, hAddOp0Type, hAddOp1Type⟩ :=
    OperationPtr.Verified.llvm_add opVerif hOpType
  have ho0Eq : o0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have ho1Eq : o1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = o0 := by
    rw [ho0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = o1 := by
    rw [ho1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have ho0Type : (o0.getType! ctx.raw).val = Attribute.integerType addIntType := by
    rw [← hOperand0, hAddOp0Type]
  have ho1Type : (o1.getType! ctx.raw).val = Attribute.integerType addIntType := by
    rw [← hOperand1, hAddOp1Type]
  -- Peel the defining `shl` of `shlNeg := if commuted then o0 else o1`.
  have hDefShlSome : (getDefiningOp (if commuted then o0 else o1) ctx.raw).isSome := by
    cases hM : getDefiningOp (if commuted then o0 else o1) ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dShl, hDefShl⟩ := Option.isSome_iff_exists.mp hDefShlSome
  rw [hDefShl] at hpattern
  simp only [] at hpattern
  have hShlSome : (matchShl dShl ctx.raw).isSome := by
    cases hM : matchShl dShl ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨negB, c, shProps⟩, hShl⟩ := Option.isSome_iff_exists.mp hShlSome
  rw [hShl] at hpattern
  simp only [] at hpattern
  -- Peel the defining `sub` of `negB`.
  have hDefSubSome : (getDefiningOp negB ctx.raw).isSome := by
    cases hM : getDefiningOp negB ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dSub, hDefSub⟩ := Option.isSome_iff_exists.mp hDefSubSome
  rw [hDefSub] at hpattern
  simp only [] at hpattern
  have hSubSome : (matchSub dSub ctx.raw).isSome := by
    cases hM : matchSub dSub ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨zeroV, b, subProps⟩, hSub⟩ := Option.isSome_iff_exists.mp hSubSome
  rw [hSub] at hpattern
  simp only [] at hpattern
  -- Peel the constant match and its `= 0` guard.
  have hZCSome : (matchConstantIntVal zeroV ctx.raw).isSome := by
    cases hM : matchConstantIntVal zeroV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨zc, hZC⟩ := Option.isSome_iff_exists.mp hZCSome
  rw [hZC] at hpattern
  simp only [] at hpattern
  -- The initial `simp [pure]` flips the negated `if` guards, so the surviving condition is the
  -- positive form and the bail branch is the `else`.
  have hZCval : zc.value = 0 := by
    rcases Decidable.em (zc.value = 0) with h0 | hne
    · exact h0
    · rw [if_neg hne] at hpattern; simp at hpattern
  rw [if_pos hZCval] at hpattern
  -- Peel the `c : i64` guard.
  obtain ⟨ct, hCTypeVal⟩ : ∃ t, (c.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (c.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hCTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse => simp at hpattern
  rename_i hCbwRaw
  -- Peel the result `i64` guard.
  obtain ⟨rt, hRTypeVal⟩ :
      ∃ t, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hRTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse => simp at hpattern
  rename_i hRbwRaw
  -- Collapse widths to `i64`.
  obtain ⟨cbw⟩ := ct; obtain ⟨rbw⟩ := rt
  simp only at hCbwRaw hRbwRaw hCTypeVal hRTypeVal
  obtain rfl : cbw = 64 := by omega
  obtain rfl : rbw = 64 := by omega
  -- `addIntType = i64` (result type), so both `add` operands are `i64`.
  have hAddIntType64 : addIntType = ⟨64⟩ := by rw [hAddResType] at hRTypeVal; grind
  subst hAddIntType64
  -- Walk the `shl (sub 0 B) C` chain.
  have hShlNegMem : (if commuted then o0 else o1) ∈ op.getOperands! ctx.raw := by
    rw [hOperands]; cases commuted <;> simp
  have hShlNegType : ((if commuted then o0 else o1).getType! ctx.raw).val
      = Attribute.integerType ⟨64⟩ := by
    cases commuted with
    | true => simpa using ho0Type
    | false => simpa using ho1Type
  obtain ⟨bv, cv, hbVal, hcVal, hShlNegVal, hbType, hDomB, hDomC, hbIn, hcIn, hbNotRes, hcNotRes⟩ :=
    shlNegChain ctxDom ctxVerif opInBounds stateWf hShlNegMem hShlNegType hDefShl hShl hCTypeVal
      hDefSub hSub hZC hZCval
  -- Unfold the matched `add`'s interpretation.
  obtain ⟨o0v, o1v, ho0Val, ho1Val, hMem, hAddRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .add)
      (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .add))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp ho0Type ho1Type
  subst hCf
  -- `shlNeg`'s value (`if commuted then o0v else o1v`) is the `shl (sub 0 B) C` chain.
  have hSnvEq : (if commuted then o0v else o1v)
      = Data.LLVM.Int.shl
          (Data.LLVM.Int.sub (Data.LLVM.Int.constant 64 0) bv subProps.nsw subProps.nuw)
          cv shProps.nsw shProps.nuw := by
    have hh := hShlNegVal
    cases commuted with
    | true => simp only [if_true] at hh ⊢; have := ho0Val.symm.trans hh; simpa using this
    | false =>
      simp only [Bool.false_eq_true, if_false] at hh ⊢
      have := ho1Val.symm.trans hh; simpa using this
  -- `a := if commuted then o1 else o0`, the non-`shl` operand of `op`. Introduce it as a local via
  -- `generalize` (both `set` and `by_contra` are unavailable in this project).
  generalize haOpDef : (if commuted then o1 else o0) = aOp at hpattern
  have haOpMem : aOp ∈ op.getOperands! ctx.raw := by
    rw [hOperands, ← haOpDef]; cases commuted <;> simp
  have hDomA : aOp.dominatesIp (InsertPoint.before op) ctx :=
    ctxDom.operand_dominates_op opInBounds haOpMem
  have hAIn : aOp.InBounds ctx.raw := by
    rw [← haOpDef]; cases commuted <;> (simp only [Bool.false_eq_true, if_false, if_true]) <;>
      grind [OperationPtr.getOperands!]
  have hANotRes : aOp ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl aOp haOpMem
  have hAVal : state.variables.getVar? aOp
      = some (RuntimeValue.int 64 (if commuted then o1v else o0v)) := by
    rw [← haOpDef]; cases commuted with
    | true => simpa using ho1Val
    | false => simpa using ho0Val
  -- Source value: `add o0v o1v aProps`.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hAddRes] at hsourceValues
  subst sourceValues
  -- Peel the two created ops (`shl B C`, then `sub a shl`).
  peelOpCreation!₃ hpattern ctx₁ newShl hNewShl hDomA hDomA₁ hDomB hDomB₁ hDomC hDomC₁
  peelOpCreation!₃ hpattern ctx₂ newOp hNewOp hDomA₁ hDomA₂ hDomB₁ hDomB₂ hDomC₁ hDomC₂
  cleanupHpattern hpattern
  have hNewShlNeNewOp : newShl ≠ newOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- Structural facts: the created `shl B C`.
  have hbTypeAttr : b.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hbType ▸ (b.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hbType
  have hNewShlType : newShl.getOpType! ctx₂.raw = .llvm .shl := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNewShl (operation := newShl),
      OperationPtr.getOpType!_WfRewriter_createOp hNewOp (operation := newShl)]
  have hNewShlOperands : newShl.getOperands! ctx₂.raw = #[b, c] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNewShl (operation := newShl),
      OperationPtr.getOperands!_WfRewriter_createOp hNewOp (operation := newShl)]
  have hNewShlProps : newShl.getProperties! ctx₂.raw (.llvm .shl) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNewShl (operation := newShl),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hNewOp hNewShlNeNewOp]
  have hNewShlResTypes : newShl.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hbType ▸ (b.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNewShl (operation := newShl)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hNewOp (operation := newShl)
    rw [if_neg hNewShlNeNewOp] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hbTypeAttr
  -- Structural facts: the created `sub a shl`.
  have hOpResTypeAttr : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType ⟨64⟩, hRTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) :=
    Subtype.ext hRTypeVal
  have hGetTypeEq : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hRTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact hOpResTypeAttr
  have hGetTypeEq₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨64⟩, hRTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [← hGetTypeEq]
    grind [ValuePtr.getType!_WfRewriter_createOp hNewShl
      (value := ValuePtr.opResult (op.getResult 0))]
  have hNewOpType : newOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNewOp (operation := newOp)]
  have hNewOpOperands : newOp.getOperands! ctx₂.raw = #[aOp, ValuePtr.opResult (newShl.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNewOp (operation := newOp)]
  have hNewOpProps : newOp.getProperties! ctx₂.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNewOp (operation := newOp)]
  have hNewOpResTypes : newOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hRTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNewOp (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hGetTypeEq₁
  -- Read the refined `a`/`b`/`c` in the target state.
  obtain ⟨atv, hAVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hAIn hAVal
      hDomA hDomA₂ hANotRes
  obtain ⟨btv, hBVal', hbRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hbIn hbVal
      hDomB hDomB₂ hbNotRes
  obtain ⟨ctv, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hcIn hcVal
      hDomC hDomC₂ hcNotRes
  -- Replay the `shl`, then the `sub`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.shl x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNewShlType hNewShlProps hNewShlOperands hNewShlResTypes hBVal' hCVal'
  have hAVal₁ : s₁.variables.getVar? aOp = some (RuntimeValue.int 64 atv) := by
    rw [hFrame₁ aOp (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hAIn
      (WfRewriter.createOp_new_not_inBounds newShl hNewShl))]
    exact hAVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.sub x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNewOpType hNewOpProps hNewOpOperands hNewOpResTypes hAVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (Data.LLVM.Int.sub atv (Data.LLVM.Int.shl btv ctv false false) false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `add o0v o1v aProps ⊒ sub atv (shl btv ctv) `, via the data lemma + monotonicity.
  simp only [Data.LLVM.Int.cast_self]
  cases commuted with
  | true =>
    simp only [if_true] at hSnvEq haRef
    rw [hSnvEq]
    exact isRefinedBy_trans
      (Data.LLVM.Int.add_shift_commute (a := o1v) (b := bv) (c := cv))
      (Data.LLVM.Int.sub_mono o1v (Data.LLVM.Int.shl bv cv false false) atv
        (Data.LLVM.Int.shl btv ctv false false) haRef
        (Data.LLVM.Int.shl_mono bv cv btv ctv hbRef hcRef false false) false false)
  | false =>
    simp only [Bool.false_eq_true, if_false] at hSnvEq haRef
    rw [hSnvEq]
    exact isRefinedBy_trans
      (Data.LLVM.Int.add_shift (a := o0v) (b := bv) (c := cv))
      (Data.LLVM.Int.sub_mono o0v (Data.LLVM.Int.shl bv cv false false) atv
        (Data.LLVM.Int.shl btv ctv false false) haRef
        (Data.LLVM.Int.shl_mono bv cv btv ctv hbRef hcRef false false) false false)

theorem add_shift_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics (addShiftLocal false) h h₂ h₃ h₄ :=
  addShiftLocal_preservesSemantics

theorem add_shift_commute_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics (addShiftLocal true) h h₂ h₃ h₄ :=
  addShiftLocal_preservesSemantics

/-! ### redundant_binop_in_equality

  `(binop X Y) cmp X → Y cmp 0` for `binop ∈ {add, sub, xor}`, `cmp ∈ {eq, ne}`. `op` is the
  `icmp`, whose left operand is the result of a defining `binop`; recover that value with a generic
  Layer-3 graph lemma parameterized over the binop opcode, then create a `constant 0` and an `icmp`.
-/

set_option maxHeartbeats 1000000 in
/-- Generic version of `matchAdd_getVar?_of_EquationLemmaAt`, parameterized over the binop opcode
    `srcOp`, its data-level function `srcFn`, and the matcher/verifier/purity facts. Recovers the
    runtime value of a defining binop (`add`/`sub`/`xor`) reached through an operand of `op`. -/
private theorem matchBinop_getVar?_of_EquationLemmaAt {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x y : ValuePtr} {binOp : OperationPtr} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some binOp)
    (hMatch : match? binOp ctx.raw = some (x, y))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv yv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (srcFn xv yv (binOp.getProperties! ctx.raw (.llvm srcOp)))) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      (y.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ y.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧ y.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw ∧ y ∉ op.getResults! ctx.raw := by
  obtain ⟨hBinType, hBinNumResults, hBinOperands⟩ := hMatchImplies hMatch
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hBinOpEq : basePtr.op = binOp := by simp [getDefiningOp] at hDef; grind
  subst hBinOpEq
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hBinOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hBinVerified : basePtr.op.Verified ctx hBinOpIn := by grind
  obtain ⟨-, -, -, -, binIntType, hBinResType, hBinOperand0Type, hBinOperand1Type⟩ :=
    hVerified hBinVerified hBinType
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  have hIntTypeEq : intType = binIntType := by
    rw [hBaseTypeEq, hBinResType] at hBaseType; grind
  subst hIntTypeEq
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hBinOperands]; rfl
  have hyIdxEq : y = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hBinOperands]; rfl
  have hBinOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hBinOperand1 : basePtr.op.getOperand! ctx.raw 1 = y := by
    rw [hyIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hBinOperand0, hBinOperand0Type]
  have hyType : (y.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hBinOperand1, hBinOperand1Type]
  have hBinDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hBinOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hBinSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hBinDefines hOperand
  have hBinDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hBinPure : basePtr.op.Pure ctx.raw := hPure hBinType
  obtain ⟨cfB, hInterpBin⟩ := stateWf basePtr.op hBinOpIn hBinPure hBinDomIp
  obtain ⟨xv, yv, hxVal, hyVal, -, hBinResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := basePtr.op.getProperties! ctx.raw (.llvm srcOp))
      hBinOpIn hBinType hBinNumResults hBinOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res h
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at h
          injection h with h; injection h with h; exact h.symm)
      hInterpBin hxType hyType
  refine ⟨xv, yv, hxVal, hyVal, ?_, hxType, hyType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBaseEq, hBinResVal]; rfl
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hBinOpIn (by grind [OperationPtr.getOperands!])) hBinSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hBinOpIn (by grind [OperationPtr.getOperands!])) hBinSDom
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hBinSDom) x
      (by grind [OperationPtr.getOperands!])
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hBinSDom) y
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
/-- Variant of `matchBinop_getVar?_of_EquationLemmaAt` for a defining `binop X (const c)`: the
    second operand is a matched integer constant `c`, which is pinned so `base`'s value is
    `srcFn xv (constant c) props`. Returns only the first operand `X`'s facts (the constant is
    folded away). Uses the constant-operand pinning of `matchIcmpZero_getVar?_of_EquationLemmaAt`. -/
private theorem matchBinopSndConst_getVar?_of_EquationLemmaAt {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x c : ValuePtr} {binOp : OperationPtr} {cAttr : IntegerAttr} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some binOp)
    (hMatch : match? binOp ctx.raw = some (x, c))
    (hCst : matchConstantIntVal c ctx.raw = some cAttr)
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (srcFn xv (Data.LLVM.Int.constant intType.bitwidth cAttr.value)
          (binOp.getProperties! ctx.raw (.llvm srcOp)))) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  -- The binop's value and both operands' facts (generic lemma).
  obtain ⟨xv, cv, hxVal, hcVal, hBaseVal, hxType, hcType, hDomX, hDomC, hxIn, hcIn,
      xNotOp, cNotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt hMatchImplies hVerified hPure hSemSrc ctxDom ctxVerif
      opInBounds stateWf hDef hMatch hOperand hBaseType
  -- Pin the constant operand `c` to `constant cAttr.value`.
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hCst
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    rw [← heq]; exact Subtype.ext hcType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  -- `binOp` strictly dominates `op` (it defines `base`, an operand of `op`).
  obtain ⟨hBinType, hBinNumResults, hBinOperands⟩ := hMatchImplies hMatch
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hBinOpEq : basePtr.op = binOp := by simp [getDefiningOp] at hDef; grind
  subst hBinOpEq
  have hBinOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hBaseInb : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hBaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!, OpResultPtr.InBounds]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hBinDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hBinOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hBinSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hBinDefines hOperand
  -- `cstPtr.op` strictly dominates `binOp` (it defines the constant operand), hence `op`.
  have hCstSDomBin : cstPtr.op.strictlyDominates basePtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCstDefines (by rw [hBinOperands]; simp)
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomBin hBinSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType
      hInterpCst
  obtain rfl : cv = Data.LLVM.Int.constant intType.bitwidth cAttr.value := by
    rw [hCstEq] at hcVal; grind
  exact ⟨xv, hxVal, hBaseVal, hxType, hDomX, hxIn, xNotOp⟩

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the six `redundant_binop_in_equality` combines. Parameterized over
    the inner binop's opcode `srcOp`/function `srcFn`/matcher-verifier-purity facts, the predicate
    `pred`, and the data-refinement lemma `hRefine` (`icmp (srcFn x y props) x pred ⊒
    icmp y (constant 0) pred`). -/
theorem redundantBinopInEqualityLocal_preservesSemantics {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    {pred : Data.LLVM.IntPred}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hRefine : ∀ {w : Nat}, (w = 64 ∨ w = 32) → ∀ (x y : Data.LLVM.Int w)
        (props : propertiesOf (.llvm srcOp)),
        Data.LLVM.Int.icmp (srcFn x y props) x pred
          ⊒ Data.LLVM.Int.icmp y (Data.LLVM.Int.constant w 0) pred)
    {h : LocalRewritePattern.ReturnOps (redundantBinopInEqualityLocal match? pred)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (redundantBinopInEqualityLocal match? pred)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (redundantBinopInEqualityLocal match? pred)}
    {h₄ : LocalRewritePattern.ReturnValues (redundantBinopInEqualityLocal match? pred)} :
    LocalRewritePattern.PreservesSemantics (redundantBinopInEqualityLocal match? pred) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, redundantBinopInEqualityLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchIcmp`.
  have hMatchSome : (matchIcmp op ctx.raw).isSome := by
    cases hM : matchIcmp op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhsV, xval, ip⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchIcmp_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Predicate guard.
  have hPred : ip.predicate = pred := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hPred] at hpattern
  -- Verifier facts for the `icmp`: the two operands share a type, result is `i1`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, ⟨i1ty, hI1Ty, hI1Bw⟩, hOperandTypesEq⟩ :=
    OperationPtr.Verified.llvm_icmp opVerif hOpType
  have hLhsEq : lhsV = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hXvalEq : xval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhsV := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = xval := by
    rw [hXvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Peel the defining binop and the `x != xval` guard.
  have hDefSome : (getDefiningOp lhsV ctx.raw).isSome := by
    cases hM : getDefiningOp lhsV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨binOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hBinSome : (match? binOp ctx.raw).isSome := by
    cases hM : match? binOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y⟩, hBinMatch⟩ := Option.isSome_iff_exists.mp hBinSome
  rw [hBinMatch] at hpattern
  simp only [] at hpattern
  have hXEq : x = xval := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hXEq] at hpattern
  -- The comparison-operand type is `lhsV`'s (the binop result's) type; pin it via the binop's
  -- verifier.
  obtain ⟨binType, hBinTypeVal⟩ :
      ∃ t, (lhsV.getType! ctx.raw).val = Attribute.integerType t := by
    obtain ⟨hBinOpType, hBinNRes, -⟩ := hMatchImplies hBinMatch
    obtain ⟨bp, rfl⟩ : ∃ p, lhsV = ValuePtr.opResult p := by
      cases lhsV with
      | opResult p => exact ⟨p, rfl⟩
      | _ => simp [getDefiningOp] at hDef
    have hBinOpEq : bp.op = binOp := by simp [getDefiningOp] at hDef; grind
    subst hBinOpEq
    have hBinOpIn : bp.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
    have hV : bp.op.Verified ctx hBinOpIn := by grind
    obtain ⟨-, -, -, -, t, hRT, -, -⟩ := hVerified hV hBinOpType
    have hIdx : bp.index < bp.op.getNumResults! ctx.raw := by
      grind [OpResultPtr.inBounds_OperationPtr_getNumResults!, OpResultPtr.InBounds]
    have hBpEq : bp = bp.op.getResult 0 := by
      have hidx : bp.index = 0 := by omega
      cases bp; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
    refine ⟨t, ?_⟩
    have : (ValuePtr.opResult bp).getType! ctx.raw = ((bp.op.getResult 0).get! ctx.raw).type := by
      rw [hBpEq]; rfl
    rw [this, hRT]
  -- Recover the binop's runtime value and operands' facts. The recovered props is
  -- `binOp.getProperties!`; abbreviate it `bProps`.
  obtain ⟨xv, yv, hxVal, hyVal, hLhsVal, hxType, hyType, hDomX, hDomY, hxIn, hyIn,
      xNotOp, yNotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt hMatchImplies hVerified hPure hSemSrc ctxDom ctxVerif
      opInBounds stateWf hDef hBinMatch (by rw [hOperands]; simp) hBinTypeVal
  generalize hbProps : binOp.getProperties! ctx.raw (.llvm srcOp) = bProps at hLhsVal
  -- Comparison-operand types agree, so `xval`'s type is `binType` too.
  have hXvalType : (xval.getType! ctx.raw).val = Attribute.integerType binType := by
    rw [← hOperand1, ← hOperandTypesEq, hOperand0, hBinTypeVal]
  -- Width guard on `y`'s type (= `binType`).
  rw [hyType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : binType.bitwidth = 64 ∨ binType.bitwidth = 32 := by omega
  -- Unfold the matched `icmp`.
  obtain ⟨lv, xvv, hlvVal, hxvvVal, hMem, hRes, hCf⟩ :=
    matchIcmp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hinterp
      hBinTypeVal hXvalType
  subst hCf
  -- Pin `lv = srcFn xv yv bProps` and `xvv = xv` (from `x = xval`).
  obtain rfl : lv = srcFn xv yv bProps := by
    have := hlvVal.symm.trans hLhsVal; simpa using this
  obtain rfl : xv = xvv := by
    have := (hXEq ▸ hxVal).symm.trans hxvvVal; simpa using this
  -- Rewrite the icmp result's predicate `ip.predicate` to `pred` in `hRes`.
  rw [hPred] at hRes
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the two creations: the constant, then the `icmp`.
  peelOpCreation! hpattern ctx₁ c0Op hC0 hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ icmpOp hIcmp hDomY₁ hDomY₂
  cleanupHpattern hpattern
  -- Structural facts for the constant.
  have hC0Type : c0Op.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hIcmp (operation := c0Op)]
  have hC0Operands : c0Op.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hIcmp (operation := c0Op)]
  have hC0NeIcmp : c0Op ≠ icmpOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hC0Props : (c0Op.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨0, binType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC0 (operation := c0Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hIcmp hC0NeIcmp, h1]
  -- The constant's and icmp's result-type facts.
  have hYTypeAttr : y.getType! ctx.raw
      = (⟨Attribute.integerType binType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hyType
  have hC0ResTypes : c0Op.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType binType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := c0Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hIcmp (operation := c0Op)
    rw [if_neg (by clear hpattern state'Wf state'Dom valueRefinement; grind)] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hYTypeAttr
  -- Structural facts for the icmp.
  have hIcmpType : icmpOp.getOpType! ctx₂.raw = .llvm .icmp := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  have hIcmpOperands : icmpOp.getOperands! ctx₂.raw = #[y, ValuePtr.opResult (c0Op.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  have hIcmpProps : icmpOp.getProperties! ctx₂.raw (.llvm .icmp) = IcmpProperties.mk pred := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  -- The icmp's result type is `op`'s result type (`i1`).
  have hOpResTypeAttr : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType i1ty, by grind⟩ : TypeAttr) := by
    have hrt : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType i1ty := hI1Ty
    exact Subtype.ext hrt
  have hGetTypeEq₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType i1ty, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]
    grind [ValuePtr.getType!_WfRewriter_createOp hC0 (value := ValuePtr.opResult (op.getResult 0)),
      OperationPtr.getResult]
  have hIcmpResTypes : icmpOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType i1ty, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hIcmp (operation := icmpOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hGetTypeEq₁
  -- Read the refined `y` in the target state.
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  -- Replay the constant, then the `icmp`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC0Type hC0Props hC0Operands hC0ResTypes
  have hYVal₁ : s₁.variables.getVar? y = some (RuntimeValue.int binType.bitwidth yt) := by
    rw [hFrame₁ y (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hyIn
      (WfRewriter.createOp_new_not_inBounds c0Op hC0))]
    exact hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_icmp_forward (state := s₁) (inBounds := by grind)
      (i1t := i1ty) (f := fun a b => Data.LLVM.Int.icmp a b pred) hI1Bw
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hIcmpType hIcmpProps hIcmpOperands hIcmpResTypes hYVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 1 (Data.LLVM.Int.icmp yt (Data.LLVM.Int.constant binType.bitwidth 0)
      pred)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `icmp (srcFn xv yv bProps) xv pred ⊒ icmp yv 0 pred ⊒ icmp yt 0 pred`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hWidth xv yv bProps)
    (Data.LLVM.Int.icmp_mono yv (Data.LLVM.Int.constant binType.bitwidth 0) yt
      (Data.LLVM.Int.constant binType.bitwidth 0) pred hyRef (isRefinedBy_refl _))

/-- `hMatchImplies` for a `matchBinopNoProps m` adapter, derived from the underlying matcher's
    `_implies` fact. -/
private theorem matchBinopNoProps_implies {llvmOp : Llvm}
    {m : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × propertiesOf (.llvm llvmOp))}
    (hm : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r p}, m opp c = some (l, r, p) →
        opp.getOpType! c = .llvm llvmOp ∧ opp.getNumResults! c = 1 ∧
          opp.getOperands! c = #[l, r] ∧ p = opp.getProperties! c (.llvm llvmOp))
    {opp : OperationPtr} {c : IRContext OpCode} {l r}
    (hM : matchBinopNoProps m opp c = some (l, r)) :
    opp.getOpType! c = .llvm llvmOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r] := by
  simp only [matchBinopNoProps, bind, Option.bind] at hM
  split at hM
  · simp at hM
  · rename_i p hp
    obtain ⟨hl, hr⟩ : p.1 = l ∧ p.2.1 = r := by simpa using hM
    subst hl; subst hr
    obtain ⟨h1, h2, h3, -⟩ := hm hp
    exact ⟨h1, h2, h3⟩

theorem redundant_binop_in_equality_XPlusYEqX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchAdd) .eq) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .add)
    (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
    (matchBinopNoProps_implies matchAdd_implies)
    OperationPtr.Verified.llvm_add
    OperationPtr.Pure.llvm_add
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XPlusYEqX hw)

theorem redundant_binop_in_equality_XPlusYNeX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchAdd) .ne) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .add)
    (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
    (matchBinopNoProps_implies matchAdd_implies)
    OperationPtr.Verified.llvm_add
    OperationPtr.Pure.llvm_add
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XPlusYNeX hw)

theorem redundant_binop_in_equality_XMinusYEqX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchSub) .eq) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .sub)
    (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
    (matchBinopNoProps_implies matchSub_implies)
    OperationPtr.Verified.llvm_sub
    OperationPtr.Pure.llvm_sub
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XMinusYEqX hw)

theorem redundant_binop_in_equality_XMinusYNeX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchSub) .ne) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .sub)
    (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
    (matchBinopNoProps_implies matchSub_implies)
    OperationPtr.Verified.llvm_sub
    OperationPtr.Pure.llvm_sub
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XMinusYNeX hw)

theorem redundant_binop_in_equality_XXorYEqX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchXor) .eq) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies)
    OperationPtr.Verified.llvm_xor
    OperationPtr.Pure.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XXorYEqX hw)

theorem redundant_binop_in_equality_XXorYNeX_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (redundantBinopInEqualityLocal (matchBinopNoProps matchXor) .ne) h h₂ h₃ h₄ :=
  redundantBinopInEqualityLocal_preservesSemantics
    (srcOp := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies)
    OperationPtr.Verified.llvm_xor
    OperationPtr.Pure.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.redundant_binop_in_equality_XXorYNeX hw)

/-! ### double_icmp_zero_combine

  `(icmp X 0 pred) outer (icmp Y 0 pred) → icmp (X | Y) 0 pred` for `outer ∈ {and, or}`,
  `pred ∈ {eq, ne}`. `op` is the outer `and`/`or` (on `i1`); *both* its operands are the result of
  a defining `icmp _ 0 pred`. So this is the two-branch DAG-matching exemplar: recover each
  `icmp`'s value with `matchIcmpZero_getVar?_of_EquationLemmaAt` (which additionally pins the
  compared constant to `0`), then create three ops (`or`, `constant 0`, `icmp`).
-/

set_option maxHeartbeats 1000000 in
/-- Semantic content of a defining `icmp X 0 pred` reached through an operand `cond` of `op`:
    recovers `X`'s value/facts and pins `cond`'s value to `icmp xv (constant 0) pred`. Combines the
    `icmp`-value recovery of `notCmpFold_icmp_getVar?_of_EquationLemmaAt` with the constant-operand
    pinning of `matchNot_getVar?_of_EquationLemmaAt`. -/
private theorem matchIcmpZero_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {cond x c : ValuePtr} {icmpOp : OperationPtr} {iProps : propertiesOf (.llvm .icmp)}
    {cAttr : IntegerAttr} {intType : IntegerType}
    (hDef : getDefiningOp cond ctx.raw = some icmpOp)
    (hIcmp : matchIcmp icmpOp ctx.raw = some (x, c, iProps))
    (hCst : matchConstantIntVal c ctx.raw = some cAttr)
    (hCstVal : cAttr.value = 0)
    (hOperand : cond ∈ op.getOperands! ctx.raw)
    (hXType : (x.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? cond = some (RuntimeValue.int 1
        (Data.LLVM.Int.icmp xv (Data.LLVM.Int.constant intType.bitwidth 0) iProps.predicate)) ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
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
  have hIcmpVerified : condPtr.op.Verified ctx hIcmpOpIn := by grind
  obtain ⟨-, -, -, -, -, hOperandTypesEq⟩ :=
    OperationPtr.Verified.llvm_icmp hIcmpVerified hIcmpType
  have hxEq : x = (condPtr.op.getOperands! ctx.raw)[0]! := by rw [hIcmpOperands]; rfl
  have hcEq : c = (condPtr.op.getOperands! ctx.raw)[1]! := by rw [hIcmpOperands]; rfl
  have hIcmpOperand0 : condPtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hIcmpOperand1 : condPtr.op.getOperand! ctx.raw 1 = c := by
    rw [hcEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hcType : (c.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hIcmpOperand1, ← hOperandTypesEq, hIcmpOperand0, hXType]
  -- The `icmp` has been interpreted into `state`.
  have hIcmpDefines : (ValuePtr.opResult condPtr).getDefiningOp! ctx.raw = some condPtr.op := by
    have hOwner := (ctx.wellFormed.operations condPtr.op hIcmpOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hIcmpSDom : condPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hIcmpDefines hOperand
  have hIcmpDomIp : condPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hIcmpPure : condPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_icmp hIcmpType
  obtain ⟨cfI, hInterpIcmp⟩ := stateWf condPtr.op hIcmpOpIn hIcmpPure hIcmpDomIp
  obtain ⟨xv, cv, hxVal, hcVal, -, hCondResVal, -⟩ :=
    matchIcmp_interpretOp_unfold hIcmpOpIn hIcmpType hIcmpNumResults hIcmpOperands rfl
      hInterpIcmp hXType hcType
  -- Pin the compared constant `c` to `constant 0`.
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hCst
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstIn : (ValuePtr.opResult cstPtr).InBounds ctx.raw := by
    rw [← hIcmpOperand1] at hcType ⊢; grind [OperationPtr.getOperands!]
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    rw [← heq]; exact Subtype.ext hcType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCstSDomIcmp : cstPtr.op.strictlyDominates condPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCstDefines (by rw [← hIcmpOperand1]; grind [OperationPtr.getOperands!])
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomIcmp hIcmpSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType
      hInterpCst
  have hcvEq : cv = Data.LLVM.Int.constant intType.bitwidth 0 := by
    rw [hCstEq] at hcVal; rw [hCstVal] at hCstResVal; grind
  refine ⟨xv, hxVal, ?_, ?_, ?_, ?_⟩
  · rw [hCondEq, hCondResVal, hcvEq, hIcmpProps]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hIcmpOpIn (by rw [← hIcmpOperand0]; grind [OperationPtr.getOperands!]))
      hIcmpSDom
  · rw [← hIcmpOperand0] at hXType ⊢; grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hIcmpSDom) x
      (by rw [← hIcmpOperand0]; grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the two `double_icmp_zero` combines. Parameterized over the outer
    op (`srcOp` = `and`/`or`, its `srcFn` and matcher/verifier/purity facts), the predicate `pred`,
    and the data-refinement lemma `hRefine`. -/
theorem doubleIcmpZeroLocal_preservesSemantics {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    {pred : Data.LLVM.IntPred}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hRefine : ∀ {w : Nat}, (w = 64 ∨ w = 32) → ∀ (xv yv : Data.LLVM.Int w)
        (props : propertiesOf (.llvm srcOp)),
        srcFn (Data.LLVM.Int.icmp xv (Data.LLVM.Int.constant w 0) pred)
            (Data.LLVM.Int.icmp yv (Data.LLVM.Int.constant w 0) pred) props
          ⊒ Data.LLVM.Int.icmp (Data.LLVM.Int.or xv yv false)
              (Data.LLVM.Int.constant w 0) pred)
    {h : LocalRewritePattern.ReturnOps (doubleIcmpZeroLocal match? pred)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (doubleIcmpZeroLocal match? pred)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (doubleIcmpZeroLocal match? pred)}
    {h₄ : LocalRewritePattern.ReturnValues (doubleIcmpZeroLocal match? pred)} :
    LocalRewritePattern.PreservesSemantics (doubleIcmpZeroLocal match? pred) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, doubleIcmpZeroLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op`: both operands and result share the `i1` type.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `icmp`s and their constant/predicate guards.
  have hDefLSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dL, hDefL⟩ := Option.isSome_iff_exists.mp hDefLSome
  rw [hDefL] at hpattern
  simp only [] at hpattern
  have hIcmpLSome : (matchIcmp dL ctx.raw).isSome := by
    cases hM : matchIcmp dL ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cx, ipL⟩, hIcmpL⟩ := Option.isSome_iff_exists.mp hIcmpLSome
  rw [hIcmpL] at hpattern
  simp only [] at hpattern
  have hPredL : ipL.predicate = pred := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hPredL] at hpattern
  have hCxSome : (matchConstantIntVal cx ctx.raw).isSome := by
    cases hM : matchConstantIntVal cx ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cxAttr, hCx⟩ := Option.isSome_iff_exists.mp hCxSome
  rw [hCx] at hpattern
  simp only [] at hpattern
  have hCxVal : cxAttr.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCxVal] at hpattern
  have hDefRSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dR, hDefR⟩ := Option.isSome_iff_exists.mp hDefRSome
  rw [hDefR] at hpattern
  simp only [] at hpattern
  have hIcmpRSome : (matchIcmp dR ctx.raw).isSome := by
    cases hM : matchIcmp dR ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, cy, ipR⟩, hIcmpR⟩ := Option.isSome_iff_exists.mp hIcmpRSome
  rw [hIcmpR] at hpattern
  simp only [] at hpattern
  have hPredR : ipR.predicate = pred := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hPredR] at hpattern
  have hCySome : (matchConstantIntVal cy ctx.raw).isSome := by
    cases hM : matchConstantIntVal cy ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cyAttr, hCy⟩ := Option.isSome_iff_exists.mp hCySome
  rw [hCy] at hpattern
  simp only [] at hpattern
  have hCyVal : cyAttr.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCyVal] at hpattern
  -- The `y.getType! = x.getType!` guard: the mismatched branch bails.
  have hYXTypeEq : y.getType! ctx.raw = x.getType! ctx.raw := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hYXTypeEq] at hpattern
  -- Type/width guard on `x`'s type.
  obtain ⟨cmpType, hCmpType⟩ :
      ∃ t, (x.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (x.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hYCmpType : (y.getType! ctx.raw).val = Attribute.integerType cmpType := by
    rw [hYXTypeEq]; exact hCmpType
  rw [hCmpType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : cmpType.bitwidth = 64 ∨ cmpType.bitwidth = 32 := by omega
  -- Recover both defining `icmp`s' values and `x`/`y` facts.
  obtain ⟨xv, hxVal, hv0IcmpVal, hDomX, hxIn, xNotOp⟩ :=
    matchIcmpZero_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefL hIcmpL hCx
      hCxVal (by rw [hOperands]; simp) hCmpType
  obtain ⟨yv, hyVal, hv1IcmpVal, hDomY, hyIn, yNotOp⟩ :=
    matchIcmpZero_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefR hIcmpR hCy
      hCyVal (by rw [hOperands]; simp) hYCmpType
  -- The outer op is on `i1`; collapse `opIntType`.
  have hOpBw : opIntType.bitwidth = 1 := by
    have h2 := hv0Val.symm.trans hv0IcmpVal
    simp only [Option.some.injEq, RuntimeValue.int.injEq] at h2; exact h2.1
  obtain ⟨opw⟩ := opIntType; simp only at hOpBw; subst hOpBw
  -- Pin `v0v`/`v1v` to the two `icmp`s.
  obtain rfl : v0v = Data.LLVM.Int.icmp xv (Data.LLVM.Int.constant cmpType.bitwidth 0)
      ipL.predicate := by have := hv0Val.symm.trans hv0IcmpVal; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.icmp yv (Data.LLVM.Int.constant cmpType.bitwidth 0)
      ipR.predicate := by have := hv1Val.symm.trans hv1IcmpVal; simpa using this
  rw [hPredL, hPredR] at hRes
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the three creations: `or`, constant, `icmp`.
  peelOpCreation!₂ hpattern ctx₁ orOp hOr hDomX hDomX₁ hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ c0Op hC0 hDomX₁ hDomX₂
  peelOpCreation! hpattern ctx₃ icmpOp hIcmp hDomX₂ hDomX₃
  cleanupHpattern hpattern
  -- Distinctness of the three created ops.
  have hOrNeC0 : orOp ≠ c0Op := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hOrNeIcmp : orOp ≠ icmpOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hC0NeIcmp : c0Op ≠ icmpOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- Structural facts for the `or`.
  have hOrType : orOp.getOpType! ctx₃.raw = .llvm .or := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := orOp),
      OperationPtr.getOpType!_WfRewriter_createOp hIcmp (operation := orOp)]
  have hOrOperands : orOp.getOperands! ctx₃.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := orOp),
      OperationPtr.getOperands!_WfRewriter_createOp hIcmp (operation := orOp)]
  have hOrProps : orOp.getProperties! ctx₃.raw (.llvm .or) = { disjoint := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hOr (operation := orOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hC0 hOrNeC0,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hIcmp hOrNeIcmp]
  -- `x`'s type fact as a `TypeAttr` (for the created ops' result types), transported to each ctx.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType cmpType, hCmpType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hCmpType
  have hXTypeAttr₁ : x.getType! ctx₁.raw
      = (⟨Attribute.integerType cmpType, hCmpType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hOr hxIn]; exact hXTypeAttr
  have hOrResTypes : orOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType cmpType, hCmpType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hOr (operation := orOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := orOp)
    rw [if_neg hOrNeC0] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hIcmp (operation := orOp)
    rw [if_neg hOrNeIcmp] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts for the constant.
  have hC0Type : c0Op.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hIcmp (operation := c0Op)]
  have hC0Operands : c0Op.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hIcmp (operation := c0Op)]
  have hC0Props : (c0Op.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨0, cmpType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC0 (operation := c0Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hIcmp hC0NeIcmp, h1]
  have hC0ResTypes : c0Op.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType cmpType, hCmpType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := c0Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hIcmp (operation := c0Op)
    rw [if_neg hC0NeIcmp] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr₁
  -- Structural facts for the emitted `icmp`. Its result type is `op`'s result type (`i1`).
  have hIcmpType : icmpOp.getOpType! ctx₃.raw = .llvm .icmp := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  have hIcmpOperands : icmpOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (orOp.getResult 0), ValuePtr.opResult (c0Op.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  have hIcmpProps : icmpOp.getProperties! ctx₃.raw (.llvm .icmp) = IcmpProperties.mk pred := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hIcmp (operation := icmpOp)]
  -- `op`'s result type is `i1` (the outer `and`/`or` verifier gave result type = `opIntType = ⟨1⟩`).
  have hOpResI1 : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr) := hOpResType
  have hOpResGetType : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact hOpResI1
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpRes0In₁ : (ValuePtr.opResult (op.getResult 0)).InBounds ctx₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .value (ValuePtr.opResult (op.getResult 0)))
      hOr hOpRes0In
  have hOpResGetType₂ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
      = (⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC0 hOpRes0In₁,
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hOr hOpRes0In]
    exact hOpResGetType
  have hIcmpResTypes : icmpOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hIcmp (operation := icmpOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResGetType₂
  -- Read refined `x`/`y` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₃ xNotOp
  have hDomY₃ : y.dominatesIp (InsertPoint.before op) ctx₃ := by
    have := (ValuePtr.dominatesIp_before_WfRewriter_createOp hIcmp
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr
      ((ValuePtr.dominatesIp_before_WfRewriter_createOp hC0
        (by clear valueRefinement state'Dom state'Wf hpattern; grind)
        (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁)
    exact this
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₃ yNotOp
  -- Replay the `or`, then the constant, then the `icmp`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.or a b false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hOrType hOrProps hOrOperands hOrResTypes hXVal' hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_constant_forward (state := s₁) (inBounds := by grind)
      hC0Type hC0Props hC0Operands hC0ResTypes
  have hOrNumRes : orOp.getNumResults! ctx₁.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hOr (operation := orOp), if_pos rfl]; rfl
  have hOrResIn : (ValuePtr.opResult (orOp.getResult 0)).InBounds ctx₁.raw := by
    have hnr := hOrNumRes
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨WfRewriter.createOp_new_inBounds orOp hOr, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOrRes₂ : s₂.variables.getVar? (ValuePtr.opResult (orOp.getResult 0))
      = some (RuntimeValue.int cmpType.bitwidth (Data.LLVM.Int.or xt yt false)) := by
    rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hOrResIn
      (WfRewriter.createOp_new_not_inBounds c0Op hC0))]
    exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_icmp_forward (state := s₂) (inBounds := by grind)
      (i1t := ⟨1⟩) (f := fun a b => Data.LLVM.Int.icmp a b pred) rfl
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hIcmpType hIcmpProps hIcmpOperands hIcmpResTypes hOrRes₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 1 (Data.LLVM.Int.icmp (Data.LLVM.Int.or xt yt false)
      (Data.LLVM.Int.constant cmpType.bitwidth 0) pred)],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (icmp xv 0 pred) (icmp yv 0 pred) props ⊒ icmp (or xv yv false) 0 pred`,
  -- then monotonicity through the refined `xt`/`yt`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hWidth xv yv _)
    (Data.LLVM.Int.icmp_mono (Data.LLVM.Int.or xv yv false)
      (Data.LLVM.Int.constant cmpType.bitwidth 0) (Data.LLVM.Int.or xt yt false)
      (Data.LLVM.Int.constant cmpType.bitwidth 0) pred
      (Data.LLVM.Int.or_mono xv yv xt yt false hxRef hyRef) (isRefinedBy_refl _))

theorem double_icmp_zero_and_combine_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (doubleIcmpZeroLocal (matchBinopNoProps matchAnd) .eq) h h₂ h₃ h₄ :=
  doubleIcmpZeroLocal_preservesSemantics
    (srcOp := .and) (srcFn := fun a b _ => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies)
    OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.double_icmp_zero_and_combine hw)

theorem double_icmp_zero_or_combine_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (doubleIcmpZeroLocal (matchBinopNoProps matchOr) .ne) h h₂ h₃ h₄ :=
  doubleIcmpZeroLocal_preservesSemantics
    (srcOp := .or) (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (matchBinopNoProps_implies matchOr_implies)
    OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun hw _ _ _ => Data.LLVM.Int.double_icmp_zero_or_combine hw)

/-! ### NotAPlusNegOne

  `not (add X (-1)) → 0 - X`. `op` is the `xor _, -1` (matched via `matchNot` on its own result),
  whose non-constant operand is the result of a defining `add X (-1)`. Recover the `add`'s value
  (with its `-1` operand pinned) via `matchBinopSndConst_getVar?_of_EquationLemmaAt`, pin the
  outer `xor`'s own `-1`, then create a `constant 0` and a `sub 0 X` carrying the `add`'s flags.
-/

set_option maxHeartbeats 1000000 in
theorem NotAPlusNegOne_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps NotAPlusNegOne_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges NotAPlusNegOne_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds NotAPlusNegOne_local}
    {h₄ : LocalRewritePattern.ReturnValues NotAPlusNegOne_local} :
    LocalRewritePattern.PreservesSemantics NotAPlusNegOne_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, NotAPlusNegOne_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchNot (op.getResult 0)`: `op` is the `xor _, -1`.
  have hNotSome : (matchNot (op.getResult 0) ctx.raw).isSome := by
    cases hM : matchNot (op.getResult 0) ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addVal, hNot⟩ := Option.isSome_iff_exists.mp hNotSome
  obtain ⟨opResultPtr, xorRhs, xorCst, hResEq, hXori, hXorCstMatch, hXorCstVal⟩ :=
    matchNot_implies hNot
  have hOpEq : opResultPtr.op = op := by
    have : (ValuePtr.opResult (op.getResult 0)) = ValuePtr.opResult opResultPtr := hResEq
    simp only [OperationPtr.getResult, ValuePtr.opResult.injEq] at this
    grind
  rw [hOpEq] at hXori
  obtain ⟨hXorType, hXorNumResults, hXorOperands⟩ := matchXori_implies hXori
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hNot] at hpattern
  simp only [] at hpattern
  -- Peel the defining `add` and the constant `-1` guard.
  have hDefSome : (getDefiningOp addVal ctx.raw).isSome := by
    cases hM : getDefiningOp addVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cm1, ap⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  have hCm1Some : (matchConstantIntVal cm1 ctx.raw).isSome := by
    cases hM : matchConstantIntVal cm1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cm1Attr, hCm1⟩ := Option.isSome_iff_exists.mp hCm1Some
  rw [hCm1] at hpattern
  simp only [] at hpattern
  have hCm1Val : cm1Attr.value = -1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCm1Val] at hpattern
  -- Verifier facts for `op` (the `xor`): operands/result share type `xorType`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, xorType, hXorResType, hXorOperand0Type, hXorOperand1Type⟩ :=
    OperationPtr.Verified.llvm_xor opVerif hXorType
  have hAddValEq : addVal = (op.getOperands! ctx.raw)[0]! := by rw [hXorOperands]; rfl
  have hXorRhsEq : xorRhs = (op.getOperands! ctx.raw)[1]! := by rw [hXorOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = addVal := by
    rw [hAddValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = xorRhs := by
    rw [hXorRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAddValType : (addVal.getType! ctx.raw).val = Attribute.integerType xorType := by
    rw [← hOperand0, hXorOperand0Type]
  have hXorRhsType : (xorRhs.getType! ctx.raw).val = Attribute.integerType xorType := by
    rw [← hOperand1, hXorOperand1Type]
  -- Unfold the outer `xor`'s interpretation.
  obtain ⟨addValVal, xorRhsVal, hAddValVal, hXorRhsVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .xor)
      (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
      (props := op.getProperties! ctx.raw (.llvm .xor))
      opInBounds hXorType hXorNumResults hXorOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hAddValType hXorRhsType
  subst hCf
  -- Recover the defining `add X (-1)`'s value (with the `-1` pinned), and `X`'s facts. The graph
  -- lemma pins the add's props to `addOp.getProperties!`, which is exactly `ap` (via `matchAdd`).
  obtain ⟨xv, hxVal, hAddValIs, hxType, hDomX, hxIn, xNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .add)
      (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchAdd_implies)
      OperationPtr.Verified.llvm_add OperationPtr.Pure.llvm_add
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchAdd addOp ctx.raw = some (x, cm1) by
        simp only [matchBinopNoProps, bind, Option.bind, hAdd])
      hCm1 (by rw [hXorOperands]; simp) hAddValType
  have hApEq : addOp.getProperties! ctx.raw (.llvm .add) = ap := ((matchAdd_implies hAdd).2.2.2).symm
  rw [hApEq] at hAddValIs
  -- Pin `addValVal` and the outer `xor`'s `-1`.
  obtain rfl : addValVal
      = Data.LLVM.Int.add xv (Data.LLVM.Int.constant xorType.bitwidth cm1Attr.value)
          ap.nsw ap.nuw := by
    have := hAddValVal.symm.trans hAddValIs; simpa using this
  have hXorRhsConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hXorCstMatch (by rw [hXorOperands]; simp) hXorRhsType
  obtain rfl : xorRhsVal = Data.LLVM.Int.constant xorType.bitwidth xorCst.value := by
    have := hXorRhsVal.symm.trans hXorRhsConst; simpa using this
  -- Collapse the pinned constants to `-1`.
  rw [hCm1Val, hXorCstVal] at hRes
  -- Width guard on `x`'s type.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : xorType.bitwidth = 64 ∨ xorType.bitwidth = 32 := by omega
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the two creations: the constant `0`, then the `sub`.
  peelOpCreation! hpattern ctx₁ c0Op hC0 hDomX hDomX₁
  peelOpCreation! hpattern ctx₂ subOp hSub hDomX₁ hDomX₂
  cleanupHpattern hpattern
  have hC0NeSub : c0Op ≠ subOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `x`'s type as a `TypeAttr`, transported to `ctx₁`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType xorType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hXTypeAttr₁ : x.getType! ctx₁.raw
      = (⟨Attribute.integerType xorType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC0 hxIn]; exact hXTypeAttr
  -- Structural facts for the constant.
  have hC0Type : c0Op.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := c0Op)]
  have hC0Operands : c0Op.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := c0Op)]
  have hC0Props : (c0Op.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨0, xorType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC0 (operation := c0Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSub hC0NeSub, h1]
  have hC0ResTypes : c0Op.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType xorType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := c0Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := c0Op)
    rw [if_neg hC0NeSub] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts for the `sub`.
  have hSubType : subOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubOperands : subOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (c0Op.getResult 0), x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubProps : subOp.getProperties! ctx₂.raw (.llvm .sub) = ap := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSub (operation := subOp)]
  have hSubResTypes : subOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType xorType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := subOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hXTypeAttr₁
  -- Read the refined `x` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  -- Replay the constant, then the `sub`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC0Type hC0Props hC0Operands hC0ResTypes
  have hXVal₁ : s₁.variables.getVar? x = some (RuntimeValue.int xorType.bitwidth xt) := by
    rw [hFrame₁ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hxIn
      (WfRewriter.createOp_new_not_inBounds c0Op hC0))]
    exact hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.sub a b ap.nsw ap.nuw)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubType hSubProps hSubOperands hSubResTypes hRes₁ hXVal₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int xorType.bitwidth
      (Data.LLVM.Int.sub (Data.LLVM.Int.constant xorType.bitwidth 0) xt ap.nsw ap.nuw)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `xor (add xv (-1) ..) (-1) ⊒ sub 0 xv .. ⊒ sub 0 xt ..`.
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.NotAPlusNegOne_rw hWidth)
    (Data.LLVM.Int.sub_mono _ _ _ _ (isRefinedBy_refl _) hxRef ap.nsw ap.nuw)

/-! ### xor_of_and_with_same_reg

  `(x & y) ^ y → (~x) & y`. `op` is the `xor`, whose first operand is the result of a defining
  `and x y` sharing the second operand `y`. Recover the `and`'s value via
  `matchBinop_getVar?_of_EquationLemmaAt`, then create three ops — `constant -1`, `xor x (-1)`
  (`~x`), and `and (~x) y`.
-/

set_option maxHeartbeats 1000000 in
theorem xor_of_and_with_same_reg_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps xor_of_and_with_same_reg_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges xor_of_and_with_same_reg_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds xor_of_and_with_same_reg_local}
    {h₄ : LocalRewritePattern.ReturnValues xor_of_and_with_same_reg_local} :
    LocalRewritePattern.PreservesSemantics xor_of_and_with_same_reg_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, xor_of_and_with_same_reg_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchXor`.
  have hMatchSome : (matchXor op ctx.raw).isSome := by
    cases hM : matchXor op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨andVal, yval, xp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchXor_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op` (the `xor`).
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_xor opVerif hOpType
  have hAndValEq : andVal = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hYvalEq : yval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = andVal := by
    rw [hAndValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = yval := by
    rw [hYvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAndValType : (andVal.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hYvalType : (yval.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer `xor`'s interpretation.
  obtain ⟨andValVal, yvalVal, hAndValVal, hYvalVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .xor)
      (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
      (props := op.getProperties! ctx.raw (.llvm .xor))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hAndValType hYvalType
  subst hCf
  -- Peel the defining `and` and the `y2 = yval` guard.
  have hDefSome : (getDefiningOp andVal ctx.raw).isSome := by
    cases hM : getDefiningOp andVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨andOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAndSome : (matchAnd andOp ctx.raw).isSome := by
    cases hM : matchAnd andOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y2, andP⟩, hAnd⟩ := Option.isSome_iff_exists.mp hAndSome
  rw [hAnd] at hpattern
  simp only [] at hpattern
  have hY2Eq : y2 = yval := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hY2Eq] at hpattern
  -- Recover the defining `and`'s value and `x`'s facts.
  obtain ⟨xv, yv, hxVal, hy2Val, hAndValIs, hxType, hy2Type, hDomX, hDomY2, hxIn, hy2In,
      xNotOp, y2NotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .and)
      (srcFn := fun a b _ => Data.LLVM.Int.and a b)
      (matchBinopNoProps_implies matchAnd_implies)
      OperationPtr.Verified.llvm_and OperationPtr.Pure.llvm_and
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchAnd andOp ctx.raw = some (x, y2) by
        simp only [matchBinopNoProps, bind, Option.bind, hAnd])
      (by rw [hOperands]; simp) hAndValType
  -- `y2 = yval`, so `yvalVal = yv`; pin `andValVal` to `and xv yvalVal`.
  have hyvEq : yvalVal = yv := by
    have := hYvalVal.symm.trans (hY2Eq ▸ hy2Val); simpa using this
  have hAndValValEq : andValVal = Data.LLVM.Int.and xv yvalVal := by
    rw [hyvEq]; have := hAndValVal.symm.trans hAndValIs; simpa using this
  rw [hAndValValEq] at hRes
  -- Width guard on `x`'s type.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : opIntType.bitwidth = 64 ∨ opIntType.bitwidth = 32 := by omega
  -- `yval`'s facts in the source (needed for the emitted `and`).
  have hDomYval : yval.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hYvalIn : yval.InBounds ctx.raw := by grind
  have yvalNotOp : ¬ yval ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the three creations, transporting `x` and `yval` dominance through each.
  peelOpCreation!₂ hpattern ctx₁ c1Op hC1 hDomX hDomX₁ hDomYval hDomYval₁
  peelOpCreation!₂ hpattern ctx₂ notxOp hNotx hDomX₁ hDomX₂ hDomYval₁ hDomYval₂
  peelOpCreation!₂ hpattern ctx₃ andOpNew hAndNew hDomX₂ hDomX₃ hDomYval₂ hDomYval₃
  cleanupHpattern hpattern
  have hC1NeNotx : c1Op ≠ notxOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hC1NeAnd : c1Op ≠ andOpNew := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hNotxNeAnd : notxOp ≠ andOpNew := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `x`'s type as a `TypeAttr`, transported to `ctx₁`/`ctx₂`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC1 hxIn
  have hxIn₁ : x.InBounds ctx₁.raw := WfRewriter.createOp_inBounds_mono
    (ptr := .value x) hC1 hxIn
  have hXGet₂ : x.getType! ctx₂.raw = x.getType! ctx.raw := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hNotx hxIn₁, hXGet₁]
  -- Structural facts for the constant `-1`.
  have hC1Type : c1Op.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC1 (operation := c1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hNotx (operation := c1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hAndNew (operation := c1Op)]
  have hC1Operands : c1Op.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC1 (operation := c1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hNotx (operation := c1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hAndNew (operation := c1Op)]
  have hC1Props : (c1Op.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨-1, opIntType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC1 (operation := c1Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAndNew hC1NeAnd,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hNotx hC1NeNotx, h1]
  have hC1ResTypes : c1Op.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC1 (operation := c1Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hNotx (operation := c1Op)
    rw [if_neg hC1NeNotx] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAndNew (operation := c1Op)
    rw [if_neg hC1NeAnd] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts for the `xor x (-1)` (= `~x`).
  have hNotxType : notxOp.getOpType! ctx₃.raw = .llvm .xor := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNotx (operation := notxOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAndNew (operation := notxOp)]
  have hNotxOperands : notxOp.getOperands! ctx₃.raw = #[x, ValuePtr.opResult (c1Op.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNotx (operation := notxOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAndNew (operation := notxOp)]
  have hNotxProps : notxOp.getProperties! ctx₃.raw (.llvm .xor) = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNotx (operation := notxOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAndNew hNotxNeAnd]
  have hNotxResTypes : notxOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNotx (operation := notxOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAndNew (operation := notxOp)
    rw [if_neg hNotxNeAnd] at hT3
    rw [hT3, hT, hXGet₁]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts for the `and (~x) yval`.
  have hAndNewType : andOpNew.getOpType! ctx₃.raw = .llvm .and := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAndNew (operation := andOpNew)]
  have hAndNewOperands : andOpNew.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (notxOp.getResult 0), yval] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAndNew (operation := andOpNew)]
  have hAndNewProps : andOpNew.getProperties! ctx₃.raw (.llvm .and) = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAndNew (operation := andOpNew)]
  have hAndNewResTypes : andOpNew.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAndNew (operation := andOpNew)
    rw [if_pos rfl] at hT
    rw [hT, hXGet₂]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Read refined `x`/`yval` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₃ xNotOp
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hYvalIn hYvalVal
      hDomYval hDomYval₃ yvalNotOp
  -- Replay the constant, the `~x`, then the `and`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC1Type hC1Props hC1Operands hC1ResTypes
  have hXVal₁ : s₁.variables.getVar? x = some (RuntimeValue.int opIntType.bitwidth xt) := by
    rw [hFrame₁ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hxIn
      (WfRewriter.createOp_new_not_inBounds c1Op hC1))]
    exact hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.xor a b)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNotxType hNotxProps hNotxOperands hNotxResTypes hXVal₁ hRes₁
  have hYvalRes₂ : s₂.variables.getVar? yval = some (RuntimeValue.int opIntType.bitwidth yt) := by
    rw [hFrame₂ yval (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      (WfRewriter.createOp_inBounds_mono (ptr := .value yval) hC1 hYvalIn)
      (WfRewriter.createOp_new_not_inBounds notxOp hNotx))]
    rw [hFrame₁ yval (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hYvalIn
      (WfRewriter.createOp_new_not_inBounds c1Op hC1))]
    exact hYVal'
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₂) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.and a b)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAndNewType hAndNewProps hAndNewOperands hAndNewResTypes hRes₂ hYvalRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntType.bitwidth
      (Data.LLVM.Int.and (Data.LLVM.Int.xor xt (Data.LLVM.Int.constant opIntType.bitwidth (-1))) yt)],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `xor (and xv yvalVal) yvalVal ⊒ and (xor xv (-1)) yvalVal ⊒ and (xor xt (-1)) yt`.
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.xor_of_and_with_same_reg hWidth)
    (Data.LLVM.Int.and_mono _ _ _ _
      (Data.LLVM.Int.xor_mono xv (Data.LLVM.Int.constant opIntType.bitwidth (-1)) xt
        (Data.LLVM.Int.constant opIntType.bitwidth (-1)) hxRef (isRefinedBy_refl _))
      hyRef)

/-! ### sub_one_from_sub

  `(A - B) - 1 → (~B) + A`. `op` is the outer `sub`, whose second operand is the constant `1`
  (pinned via `matchConstantIntVal_getVar?`) and whose first operand is the result of a defining
  `sub A B` (recovered via `matchBinop_getVar?`). It creates a `constant -1`, `xor B (-1)` (`~B`),
  and `add (~B) A` with cleared flags.
-/

set_option maxHeartbeats 1000000 in
theorem sub_one_from_sub_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sub_one_from_sub_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sub_one_from_sub_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sub_one_from_sub_local}
    {h₄ : LocalRewritePattern.ReturnValues sub_one_from_sub_local} :
    LocalRewritePattern.PreservesSemantics sub_one_from_sub_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sub_one_from_sub_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchSub` (the outer sub).
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨subVal, c1v, sp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hSubProps⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op` (the outer sub).
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hOpType
  have hSubValEq : subVal = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hC1vEq : c1v = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = subVal := by
    rw [hSubValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = c1v := by
    rw [hC1vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hSubValType : (subVal.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hC1vType : (c1v.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer sub's interpretation.
  obtain ⟨subValVal, c1vVal, hSubValVal, hC1vVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hSubValType hC1vType
  subst hCf
  -- Peel the constant `1` guard.
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1Match⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1Match] at hpattern
  simp only [] at hpattern
  have hC1Val : c1Attr.value = 1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hC1Val] at hpattern
  -- Peel the defining inner `sub`.
  have hDefSome : (getDefiningOp subVal ctx.raw).isSome := by
    cases hM : getDefiningOp subVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨innerSub, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hInnerSome : (matchSub innerSub ctx.raw).isSome := by
    cases hM : matchSub innerSub ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, y, isp⟩, hInner⟩ := Option.isSome_iff_exists.mp hInnerSome
  rw [hInner] at hpattern
  simp only [] at hpattern
  -- Recover the inner sub's value and `x`/`y` facts.
  obtain ⟨xv, yv, hxVal, hyVal, hInnerValIs, hxType, hyType, hDomX, hDomY, hxIn, hyIn,
      xNotOp, yNotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchSub_implies)
      OperationPtr.Verified.llvm_sub OperationPtr.Pure.llvm_sub
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchSub innerSub ctx.raw = some (x, y) by
        simp only [matchBinopNoProps, bind, Option.bind, hInner])
      (by rw [hOperands]; simp) hSubValType
  -- Pin `subValVal` and the outer constant `1`.
  have hInnerValEq : subValVal
      = Data.LLVM.Int.sub xv yv (innerSub.getProperties! ctx.raw (.llvm .sub)).nsw
          (innerSub.getProperties! ctx.raw (.llvm .sub)).nuw := by
    have := hSubValVal.symm.trans hInnerValIs; simpa using this
  have hC1Const := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC1Match (by rw [hOperands]; simp) hC1vType
  have hc1vEq : c1vVal = Data.LLVM.Int.constant opIntType.bitwidth c1Attr.value := by
    have := hC1vVal.symm.trans hC1Const; simpa using this
  rw [hInnerValEq, hc1vEq, hC1Val] at hRes
  -- Width guard on `y`'s type.
  rw [hyType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : opIntType.bitwidth = 64 ∨ opIntType.bitwidth = 32 := by omega
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `y`'s type as a `TypeAttr`.
  have hYTypeAttr : y.getType! ctx.raw
      = (⟨Attribute.integerType opIntType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hyType
  -- Peel the three creations, transporting `x` and `y` dominance through each.
  peelOpCreation!₂ hpattern ctx₁ cm1Op hCm1 hDomX hDomX₁ hDomY hDomY₁
  peelOpCreation!₂ hpattern ctx₂ xorOp hXor hDomX₁ hDomX₂ hDomY₁ hDomY₂
  peelOpCreation!₂ hpattern ctx₃ addOp hAddNew hDomX₂ hDomX₃ hDomY₂ hDomY₃
  cleanupHpattern hpattern
  have hCm1NeXor : cm1Op ≠ xorOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hCm1NeAdd : cm1Op ≠ addOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXorNeAdd : xorOp ≠ addOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hYGet₁ : y.getType! ctx₁.raw = y.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCm1 hyIn
  have hyIn₁ : y.InBounds ctx₁.raw := WfRewriter.createOp_inBounds_mono (ptr := .value y) hCm1 hyIn
  have hYGet₂ : y.getType! ctx₂.raw = y.getType! ctx.raw := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hXor hyIn₁, hYGet₁]
  -- Structural facts for the constant `-1`.
  have hCm1Type : cm1Op.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCm1 (operation := cm1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := cm1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := cm1Op)]
  have hCm1Operands : cm1Op.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCm1 (operation := cm1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := cm1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := cm1Op)]
  have hCm1Props : (cm1Op.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨-1, opIntType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCm1 (operation := cm1Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hCm1NeAdd,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hXor hCm1NeXor, h1]
  have hCm1ResTypes : cm1Op.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCm1 (operation := cm1Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := cm1Op)
    rw [if_neg hCm1NeXor] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := cm1Op)
    rw [if_neg hCm1NeAdd] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hYTypeAttr
  -- Structural facts for the `xor y (-1)` (= `~y`).
  have hXorType : xorOp.getOpType! ctx₃.raw = .llvm .xor := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := xorOp)]
  have hXorOperands : xorOp.getOperands! ctx₃.raw = #[y, ValuePtr.opResult (cm1Op.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := xorOp)]
  have hXorProps : xorOp.getProperties! ctx₃.raw (.llvm .xor) = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hXorNeAdd]
  have hXorResTypes : xorOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := xorOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := xorOp)
    rw [if_neg hXorNeAdd] at hT3
    rw [hT3, hT, hYGet₁]
    exact congrArg (fun t => #[t]) hYTypeAttr
  -- Structural facts for the `add (~y) x`.
  have hAddNewType : addOp.getOpType! ctx₃.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := addOp)]
  have hAddNewOperands : addOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (xorOp.getResult 0), x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := addOp)]
  have hAddNewProps : addOp.getProperties! ctx₃.raw (.llvm .add) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAddNew (operation := addOp)]
  have hAddNewResTypes : addOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntType, hyType ▸ (y.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := addOp)
    rw [if_pos rfl] at hT
    rw [hT, hYGet₂]
    exact congrArg (fun t => #[t]) hYTypeAttr
  -- Read refined `x`/`y` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₃ xNotOp
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₃ yNotOp
  -- Replay the constant, the `~y`, then the `add`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCm1Type hCm1Props hCm1Operands hCm1ResTypes
  have hYVal₁ : s₁.variables.getVar? y = some (RuntimeValue.int opIntType.bitwidth yt) := by
    rw [hFrame₁ y (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hyIn
      (WfRewriter.createOp_new_not_inBounds cm1Op hCm1))]
    exact hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.xor a b)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hXorType hXorProps hXorOperands hXorResTypes hYVal₁ hRes₁
  have hXVal₂ : s₂.variables.getVar? x = some (RuntimeValue.int opIntType.bitwidth xt) := by
    rw [hFrame₂ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      (WfRewriter.createOp_inBounds_mono (ptr := .value x) hCm1 hxIn)
      (WfRewriter.createOp_new_not_inBounds xorOp hXor))]
    rw [hFrame₁ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hxIn
      (WfRewriter.createOp_new_not_inBounds cm1Op hCm1))]
    exact hXVal'
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₂) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.add a b false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddNewType hAddNewProps hAddNewOperands hAddNewResTypes hRes₂ hXVal₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntType.bitwidth
      (Data.LLVM.Int.add (Data.LLVM.Int.xor yt (Data.LLVM.Int.constant opIntType.bitwidth (-1)))
        xt false false)],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `sub (sub xv yv ..) 1 .. ⊒ add (xor yv -1) xv .. ⊒ add (xor yt -1) xt ..`.
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.sub_one_from_sub_rw hWidth)
    (Data.LLVM.Int.add_mono _ _ _ _
      (Data.LLVM.Int.xor_mono yv (Data.LLVM.Int.constant opIntType.bitwidth (-1)) yt
        (Data.LLVM.Int.constant opIntType.bitwidth (-1)) hyRef (isRefinedBy_refl _))
      hxRef false false)

/-! ### select_0_1 / select_0_neg1

  `select c 0 C1 → ext (~c)`, `(C1, ext) ∈ {(1, zext), (-1, sext)}`. Peel `matchSelect`, the
  result-type/width guards and both constant arms, then create a `constant -1` (`i1`), an
  `xor c (-1)` (`~c`, `i1`), and the width-changing extension.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the two `select 0 C1 → ext (~c)` combines. Parameterized over the
    false-arm constant `fvVal`, the emitted extension `dst`/`dprops`, the width-changing function
    `f` (`hSemDst`), its monotonicity (`hMono`), and the refinement lemma (`hRefine`). -/
theorem matchSelectNotExtLocal_preservesSemantics
    {fvVal : Int} {dst : Llvm} {dprops : propertiesOf (.llvm dst)}
    {f : ∀ {w : Nat}, (1 < w) → Data.LLVM.Int 1 → Data.LLVM.Int w}
    (hSemDst : ∀ (rt : IntegerType) (hw : 1 < rt.bitwidth) (c : Data.LLVM.Int 1) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' dst dprops #[⟨.integerType rt, hIsTy⟩] #[.int 1 c] blockOperands mem
          = some (.ok (#[.int rt.bitwidth (f hw c)], mem, none)))
    (hMono : ∀ {w : Nat} (hlt : 1 < w) (c₁ c₂ : Data.LLVM.Int 1), c₁ ⊒ c₂ → f hlt c₁ ⊒ f hlt c₂)
    (hRefine : ∀ {w : Nat} (_hw : w = 64 ∨ w = 32) (hlt : 1 < w) (c : Data.LLVM.Int 1),
        Data.LLVM.Int.select c (Data.LLVM.Int.constant w 0) (Data.LLVM.Int.constant w fvVal)
          ⊒ f hlt (Data.LLVM.Int.xor c (Data.LLVM.Int.constant 1 (-1))))
    {h : LocalRewritePattern.ReturnOps (matchSelectNotExtLocal fvVal dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (matchSelectNotExtLocal fvVal dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (matchSelectNotExtLocal fvVal dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (matchSelectNotExtLocal fvVal dst dprops)} :
    LocalRewritePattern.PreservesSemantics (matchSelectNotExtLocal fvVal dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, matchSelectNotExtLocal]
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
  obtain ⟨⟨cond, tval, fval⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := matchSelect_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨hNRes, hNOper, ⟨condIt, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select opVerif hOpType
  have hCondEq : cond = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hTvEq : tval = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hFvEq : fval = (op.getOperands! ctx.raw)[2]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = tval := by
    rw [hTvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = fval := by
    rw [hFvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- Result-type and bitwidth guards.
  obtain ⟨rt, hResType⟩ :
      ∃ rt, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType rt := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : rt.bitwidth = 64 ∨ rt.bitwidth = 32 := by omega
  have hLt : 1 < rt.bitwidth := by omega
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTvType : (tval.getType! ctx.raw).val = Attribute.integerType rt := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFvType : (fval.getType! ctx.raw).val = Attribute.integerType rt := by
    rw [← hOperand2, ← hResEqF, hResType]
  -- Peel the two constant arms (`tval = 0`, `fval = fvVal`).
  have hCtSome : (matchConstantIntVal tval ctx.raw).isSome := by
    cases hM : matchConstantIntVal tval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨ctAttr, hCtMatch⟩ := Option.isSome_iff_exists.mp hCtSome
  rw [hCtMatch] at hpattern
  simp only [] at hpattern
  have hCtVal : ctAttr.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCtVal] at hpattern
  have hCfSome : (matchConstantIntVal fval ctx.raw).isSome := by
    cases hM : matchConstantIntVal fval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cfAttr, hCfMatch⟩ := Option.isSome_iff_exists.mp hCfSome
  rw [hCfMatch] at hpattern
  simp only [] at hpattern
  have hCfVal : cfAttr.value = fvVal := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCfVal] at hpattern
  -- Peel the `cond`-type match (needed to reach the creations).
  rw [hCondType] at hpattern
  simp only [] at hpattern
  -- Unfold the matched `select`.
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTvType hFvType hinterp
  subst hCf
  -- Pin the two constant arms.
  have htConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCtMatch (by rw [hOperands]; simp) hTvType
  obtain rfl : tvv = Data.LLVM.Int.constant rt.bitwidth ctAttr.value := by
    have := htVal.symm.trans htConst; simpa using this
  have hfConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCfMatch (by rw [hOperands]; simp) hFvType
  obtain rfl : fvv = Data.LLVM.Int.constant rt.bitwidth cfAttr.value := by
    have := hfVal.symm.trans hfConst; simpa using this
  rw [hCtVal, hCfVal] at hRes
  -- Dominance / freshness for `cond`.
  have hDomC : cond.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hCIn : cond.InBounds ctx.raw := by grind
  have cNotOp : ¬ cond ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `cond`'s type as a `TypeAttr` (`i1`).
  have hCondTypeAttr : cond.getType! ctx.raw
      = (⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hCondType
  -- Peel the three creations, transporting `cond` dominance through each.
  peelOpCreation! hpattern ctx₁ c1Op hC1 hDomC hDomC₁
  peelOpCreation! hpattern ctx₂ ncondOp hNcond hDomC₁ hDomC₂
  peelOpCreation! hpattern ctx₃ extOp hExt hDomC₂ hDomC₃
  cleanupHpattern hpattern
  have hC1NeNcond : c1Op ≠ ncondOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hC1NeExt : c1Op ≠ extOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hNcondNeExt : ncondOp ≠ extOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hCondGet₁ : cond.getType! ctx₁.raw = cond.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC1 hCIn
  have hCIn₁ : cond.InBounds ctx₁.raw := WfRewriter.createOp_inBounds_mono
    (ptr := .value cond) hC1 hCIn
  -- The result type (`i{rt}`) as a `TypeAttr`, transported to `ctx₂`.
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpResAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType rt, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hResType
  have hOpResAttr₂ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
      = (⟨Attribute.integerType rt, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hNcond
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hC1 hOpRes0In),
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC1 hOpRes0In]
    exact hOpResAttr
  -- Structural facts: the constant `-1`.
  have hC1Type : c1Op.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC1 (operation := c1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hNcond (operation := c1Op),
      OperationPtr.getOpType!_WfRewriter_createOp hExt (operation := c1Op)]
  have hC1Operands : c1Op.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC1 (operation := c1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hNcond (operation := c1Op),
      OperationPtr.getOperands!_WfRewriter_createOp hExt (operation := c1Op)]
  have hC1Props : (c1Op.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨-1, ⟨1⟩⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC1 (operation := c1Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hExt hC1NeExt,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hNcond hC1NeNcond, h1]
  have hC1ResTypes : c1Op.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC1 (operation := c1Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hNcond (operation := c1Op)
    rw [if_neg hC1NeNcond] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hExt (operation := c1Op)
    rw [if_neg hC1NeExt] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hCondTypeAttr
  -- Structural facts: the `xor cond (-1)` (`~cond`).
  have hNcondType : ncondOp.getOpType! ctx₃.raw = .llvm .xor := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNcond (operation := ncondOp),
      OperationPtr.getOpType!_WfRewriter_createOp hExt (operation := ncondOp)]
  have hNcondOperands : ncondOp.getOperands! ctx₃.raw
      = #[cond, ValuePtr.opResult (c1Op.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNcond (operation := ncondOp),
      OperationPtr.getOperands!_WfRewriter_createOp hExt (operation := ncondOp)]
  have hNcondProps : ncondOp.getProperties! ctx₃.raw (.llvm .xor) = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNcond (operation := ncondOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hExt hNcondNeExt]
  have hNcondResTypes : ncondOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNcond (operation := ncondOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hExt (operation := ncondOp)
    rw [if_neg hNcondNeExt] at hT3
    rw [hT3, hT, hCondGet₁]
    exact congrArg (fun t => #[t]) hCondTypeAttr
  -- Structural facts: the extension `dst (~cond)`.
  have hExtType : extOp.getOpType! ctx₃.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hExt (operation := extOp)]
  have hExtOperands : extOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (ncondOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hExt (operation := extOp)]
  have hExtProps : extOp.getProperties! ctx₃.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hExt (operation := extOp)]
  have hExtResTypes : extOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType rt,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hExt (operation := extOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResAttr₂
  -- Read the refined `cond` in the target state.
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
      hDomC hDomC₃ cNotOp
  -- Replay the constant, the `~cond`, then the extension.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC1Type hC1Props hC1Operands hC1ResTypes
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn
      (WfRewriter.createOp_new_not_inBounds c1Op hC1))]
    exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (it := ⟨1⟩) (f := fun a b => Data.LLVM.Int.xor a b)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNcondType hNcondProps hNcondOperands hNcondResTypes hCVal₁ hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₂) (inBounds := by grind)
      (srcType := ⟨1⟩) (resType := rt) (f := fun c => f hLt c)
      (by intro blockOperands mem; exact hSemDst rt hLt _ _ blockOperands mem)
      hExtType hExtProps hExtOperands hExtResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int rt.bitwidth
      (f hLt (Data.LLVM.Int.xor ct (Data.LLVM.Int.constant 1 (-1))))],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `select cv 0 fvVal ⊒ f (~cv) ⊒ f (~ct)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hWidth hLt cv)
    (hMono hLt _ _ (Data.LLVM.Int.xor_mono cv (Data.LLVM.Int.constant 1 (-1)) ct
      (Data.LLVM.Int.constant 1 (-1)) hcRef (isRefinedBy_refl _)))

theorem select_0_1_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (matchSelectNotExtLocal 1 .zext { nneg := false }) h h₂ h₃ h₄ :=
  matchSelectNotExtLocal_preservesSemantics
    (f := fun {w} hlt c => Data.LLVM.Int.zext c w false hlt)
    (fun rt hw c hIsTy bo mem => zext_interpretOp' 1 rt hw c { nneg := false } hIsTy bo mem)
    (fun hlt c₁ c₂ h => Data.LLVM.Int.zext_mono c₁ c₂ hlt h)
    (fun hw hlt _c => Data.LLVM.Int.select_0_1 hw hlt)

theorem select_0_neg1_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (matchSelectNotExtLocal (-1) .sext ()) h h₂ h₃ h₄ :=
  matchSelectNotExtLocal_preservesSemantics
    (f := fun {w} hlt c => Data.LLVM.Int.sext c w hlt)
    (fun rt hw c hIsTy bo mem => sext_interpretOp' 1 rt hw c () hIsTy bo mem)
    (fun hlt c₁ c₂ h => Data.LLVM.Int.sext_mono c₁ c₂ hlt h)
    (fun hw hlt _c => Data.LLVM.Int.select_0_neg1 hw hlt)

/-! ### hoist_logic_op (`*AndAnd`)

  `(X & Z) outer (Y & Z) → (X outer Y) & Z` for `outer ∈ {and, or, xor}`. `op` is the outer op;
  *both* its operands are the result of a defining `and _ Z` sharing `Z`. Recover both `and`s via
  `matchBinop_getVar?_of_EquationLemmaAt`, then create `inner = dst X Y` and `and inner Z`.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndAndAnd`/`OrAndAnd`/`XorAndAnd`. Parameterized over the outer
    op (`srcOp`/`srcFn`/matcher-verifier-purity), the inner emitted op `dst` computing `dfn`
    (`hSemDst`), and the data-refinement lemma `hRefine`. -/
theorem hoistAndAndLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ {w : Nat}, (w = 64 ∨ w = 32) → ∀ (xv yv zv : Data.LLVM.Int w)
        (_px _py : propertiesOf (.llvm .and)) (po : propertiesOf (.llvm srcOp)),
        srcFn (Data.LLVM.Int.and xv zv) (Data.LLVM.Int.and yv zv) po
          ⊒ Data.LLVM.Int.and (dfn xv yv) zv)
    {h : LocalRewritePattern.ReturnOps (hoistAndAndLocal match? dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistAndAndLocal match? dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistAndAndLocal match? dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistAndAndLocal match? dst dprops)} :
    LocalRewritePattern.PreservesSemantics (hoistAndAndLocal match? dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistAndAndLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `and`s and the `z0 = z1` guard.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hAndXSome : (matchAnd dX ctx.raw).isSome := by
    cases hM : matchAnd dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, z0, xandp⟩, hAndX⟩ := Option.isSome_iff_exists.mp hAndXSome
  rw [hAndX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hAndYSome : (matchAnd dY ctx.raw).isSome := by
    cases hM : matchAnd dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, z1, yandp⟩, hAndY⟩ := Option.isSome_iff_exists.mp hAndYSome
  rw [hAndY] at hpattern
  simp only [] at hpattern
  have hZEq : z0 = z1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hZEq] at hpattern
  -- Recover both defining `and`s.
  obtain ⟨xv, z0v, hxVal, hz0Val, hv0AndIs, hxType, hz0Type, hDomX, hDomZ0, hxIn, hz0In,
      xNotOp, z0NotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .and)
      (srcFn := fun a b _ => Data.LLVM.Int.and a b)
      (matchBinopNoProps_implies matchAnd_implies)
      OperationPtr.Verified.llvm_and OperationPtr.Pure.llvm_and
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDefX
      (show matchBinopNoProps matchAnd dX ctx.raw = some (x, z0) by
        simp only [matchBinopNoProps, bind, Option.bind, hAndX])
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨yv, z1v, hyVal, hz1Val, hv1AndIs, hyType, hz1Type, hDomY, hDomZ1, hyIn, hz1In,
      yNotOp, z1NotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .and)
      (srcFn := fun a b _ => Data.LLVM.Int.and a b)
      (matchBinopNoProps_implies matchAnd_implies)
      OperationPtr.Verified.llvm_and OperationPtr.Pure.llvm_and
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDefY
      (show matchBinopNoProps matchAnd dY ctx.raw = some (y, z1) by
        simp only [matchBinopNoProps, bind, Option.bind, hAndY])
      (by rw [hOperands]; simp) hv1Type
  -- `z0 = z1`, so `z0v = z1v`; pin `v0v`/`v1v`.
  have hzvEq : z1v = z0v := by
    have := hz1Val.symm.trans (hZEq ▸ hz0Val); simpa using this
  obtain rfl : v0v = Data.LLVM.Int.and xv z0v := by
    have := hv0Val.symm.trans hv0AndIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.and yv z1v := by
    have := hv1Val.symm.trans hv1AndIs; simpa using this
  rw [hzvEq] at hRes
  -- Width guard on `x`'s type.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : opIntType.bitwidth = 64 ∨ opIntType.bitwidth = 32 := by omega
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr`, transported to `ctx₁`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  -- Peel the two creations (inner `dst x y`, then `and inner z0`), transporting `x`/`y`/`z0`.
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  -- `z0` dominance through the first creation.
  have hDomZ0₁ : z0.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hInner
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomZ0
  peelOpCreation!₂ hpattern ctx₂ andNewOp hAndNew hDomX₁ hDomX₂ hDomZ0₁ hDomZ0₂
  cleanupHpattern hpattern
  have hInnerNeAnd : innerOp ≠ andNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAndNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAndNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAndNew hInnerNeAnd]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hAndNew (operation := innerOp)
    rw [if_neg hInnerNeAnd] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `and inner z0`.
  have hAndNewType : andNewOp.getOpType! ctx₂.raw = .llvm .and := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAndNew (operation := andNewOp)]
  have hAndNewOperands : andNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0), z0] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAndNew (operation := andNewOp)]
  have hAndNewProps : andNewOp.getProperties! ctx₂.raw (.llvm .and) = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAndNew (operation := andNewOp)]
  have hAndNewResTypes : andNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAndNew (operation := andNewOp)
    rw [if_pos rfl] at hT
    rw [hT, hXGet₁]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Read refined `x`/`y`/`z0` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hAndNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  obtain ⟨z0t, hZ0Val', hz0Ref⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hz0In hz0Val
      hDomZ0 hDomZ0₂ z0NotOp
  -- Replay the inner op, then the `and`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  have hZ0Res₁ : s₁.variables.getVar? z0 = some (RuntimeValue.int opIntType.bitwidth z0t) := by
    rw [hFrame₁ z0 (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      hz0In (WfRewriter.createOp_new_not_inBounds innerOp hInner))]
    exact hZ0Val'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.and a b)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAndNewType hAndNewProps hAndNewOperands hAndNewResTypes hRes₁ hZ0Res₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntType.bitwidth (Data.LLVM.Int.and (dfn xt yt) z0t)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (and xv zv) (and yv zv) ⊒ and (dfn xv yv) zv ⊒ and (dfn xt yt) z0t`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hWidth xv yv z0v xandp yandp _)
    (Data.LLVM.Int.and_mono _ _ _ _ (hMono xv xt yv yt hxRef hyRef) hz0Ref)

theorem AndAndAnd_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAndAndLocal (matchBinopNoProps matchAnd) .and ()) h h₂ h₃ h₄ :=
  hoistAndAndLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun hw x y z _ _ _ => Data.LLVM.Int.AndAndAnd hw)

theorem OrAndAnd_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAndAndLocal (matchBinopNoProps matchOr) .or { disjoint := false }) h h₂ h₃ h₄ :=
  hoistAndAndLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun hw x y z _ _ _ => Data.LLVM.Int.OrAndAnd hw)

theorem XorAndAnd_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAndAndLocal (matchBinopNoProps matchXor) .xor ()) h h₂ h₃ h₄ :=
  hoistAndAndLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun hw x y z _ _ _ => Data.LLVM.Int.XorAndAnd hw)

/-! ### hoist_logic_op (`*ZextZext`)

  `(zext X) outer (zext Y) → zext (X outer Y)` for `outer ∈ {and, or, xor}`, at `i32 → i64`. `op`
  is the outer op; *both* its operands are defining `zext`s (recovered via
  `zext_getVar?_of_EquationLemmaAt`). Create `inner = dst X Y` (`i32`) then `zext inner` (`i64`).
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndZextZext`/`OrZextZext`/`XorZextZext`. Parameterized over the
    outer op, the inner emitted op `dst`/`dfn` (`hSemDst`/`hMono`), whether the created `zext`
    reuses the second `zext`'s `nneg` (`useSndNneg`), and the refinement lemma `hRefine`. -/
theorem hoistZextLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)} {useSndNneg : Bool}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (n0 n1 : Bool) (x y : Data.LLVM.Int 32) (po : propertiesOf (.llvm srcOp))
        (hlt : (32 : Nat) < 64),
        srcFn (Data.LLVM.Int.zext x 64 n0 hlt) (Data.LLVM.Int.zext y 64 n1 hlt) po
          ⊒ Data.LLVM.Int.zext (dfn x y) 64 (if useSndNneg then n1 else false) hlt)
    {h : LocalRewritePattern.ReturnOps (hoistZextLocal match? dst dprops useSndNneg)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistZextLocal match? dst dprops useSndNneg)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistZextLocal match? dst dprops useSndNneg)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistZextLocal match? dst dprops useSndNneg)} :
    LocalRewritePattern.PreservesSemantics (hoistZextLocal match? dst dprops useSndNneg) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistZextLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ := hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `zext`s.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hZXSome : (matchZext dX ctx.raw).isSome := by
    cases hM : matchZext dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, xp⟩, hZX⟩ := Option.isSome_iff_exists.mp hZXSome
  rw [hZX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hZYSome : (matchZext dY ctx.raw).isSome := by
    cases hM : matchZext dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, yp⟩, hZY⟩ := Option.isSome_iff_exists.mp hZYSome
  rw [hZY] at hpattern
  simp only [] at hpattern
  -- Recover both `zext`s.
  obtain ⟨opTypeX, hwX, xv, hxVal, hv0ZextIs, hxType, hDomX, hxIn, xNotOp⟩ :=
    zext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefX hZX
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨opTypeY, hwY, yv, hyVal, hv1ZextIs, hyType, hDomY, hyIn, yNotOp⟩ :=
    zext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefY hZY
      (by rw [hOperands]; simp) hv1Type
  -- Width guards: `opTypeX = opTypeY = i32`, `opIntType = i64`.
  have hOpResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType := by
    rw [hOpResType]
  rw [hxType, hyType, hOpResTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hXW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hYW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  -- Collapse widths to the literals.
  obtain ⟨xw⟩ := opTypeX; simp only at hXW; subst hXW
  obtain ⟨yw⟩ := opTypeY; simp only at hYW; subst hYW
  obtain ⟨rw'⟩ := opIntType; simp only at hRW; subst hRW
  -- Pin `v0v`/`v1v` to the two zexts (both narrow at `i32`).
  obtain rfl : v0v = Data.LLVM.Int.zext xv 64 xp.nneg hwX := by
    have := hv0Val.symm.trans hv0ZextIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.zext yv 64 yp.nneg hwY := by
    have := hv1Val.symm.trans hv1ZextIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr` (`i32`), transported to `ctx₁`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  -- The result type `i64` as a `TypeAttr`, and `op`'s result in-bounds.
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpResAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hOpResTypeVal
  -- Peel the two creations (inner `dst x y : i32`, then `zext inner : i64`).
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ zextNewOp hZextNew hDomX₁ hDomX₂
  cleanupHpattern hpattern
  have hInnerNeZext : innerOp ≠ zextNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  have hOpResAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hOpRes0In]; exact hOpResAttr
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hZextNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hZextNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hZextNew hInnerNeZext]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hZextNew (operation := innerOp)
    rw [if_neg hInnerNeZext] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `zext inner`.
  have hZextNewType : zextNewOp.getOpType! ctx₂.raw = .llvm .zext := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hZextNew (operation := zextNewOp)]
  have hZextNewOperands : zextNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hZextNew (operation := zextNewOp)]
  have hZextNewProps : zextNewOp.getProperties! ctx₂.raw (.llvm .zext)
      = { nneg := if useSndNneg then yp.nneg else false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hZextNew (operation := zextNewOp)]
  have hZextNewResTypes : zextNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hZextNew (operation := zextNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResAttr₁
  -- Read refined `x`/`y` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hZextNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  -- Replay the inner op (`i32`), then the `zext` (`i32 → i64`).
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (it := ⟨32⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁) (inBounds := by grind)
      (srcType := ⟨32⟩) (resType := ⟨64⟩)
      (f := fun c => Data.LLVM.Int.zext c 64 (if useSndNneg then yp.nneg else false) (by omega))
      (by intro blockOperands mem
          exact zext_interpretOp' 32 ⟨64⟩ (by omega) _
            { nneg := if useSndNneg then yp.nneg else false } _ blockOperands mem)
      hZextNewType hZextNewProps hZextNewOperands hZextNewResTypes hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (Data.LLVM.Int.zext (dfn xt yt) 64 (if useSndNneg then yp.nneg else false) (by omega))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (zext xv) (zext yv) ⊒ zext (dfn xv yv) ⊒ zext (dfn xt yt)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine xp.nneg yp.nneg xv yv _ hwX)
    (Data.LLVM.Int.zext_mono (dfn xv yv) (dfn xt yt) (by omega) (hMono xv xt yv yt hxRef hyRef))

theorem AndZextZext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistZextLocal (matchBinopNoProps matchAnd) .and () true) h h₂ h₃ h₄ :=
  hoistZextLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun n0 n1 x y _ hlt => by simpa using Data.LLVM.Int.AndZextZext (n0 := n0) (n1 := n1))

theorem OrZextZext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistZextLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) h h₂ h₃ h₄ :=
  hoistZextLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun n0 n1 x y po hlt => by
      simpa using Data.LLVM.Int.OrZextZext (n0 := n0) (n1 := n1) (d := po.disjoint))

theorem XorZextZext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistZextLocal (matchBinopNoProps matchXor) .xor () false) h h₂ h₃ h₄ :=
  hoistZextLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun n0 n1 x y _ hlt => by simpa using Data.LLVM.Int.XorZextZext (n0 := n0) (n1 := n1))


set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndSextSext`/`OrSextSext`/`XorSextSext`. Parameterized over the
    outer op, the inner emitted op `dst`/`dfn` (`hSemDst`/`hMono`), whether and the refinement lemma `hRefine`. -/
theorem hoistSextLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (x y : Data.LLVM.Int 32) (po : propertiesOf (.llvm srcOp))
        (hlt : (32 : Nat) < 64),
        srcFn (Data.LLVM.Int.sext x 64 hlt) (Data.LLVM.Int.sext y 64 hlt) po
          ⊒ Data.LLVM.Int.sext (dfn x y) 64 hlt)
    {h : LocalRewritePattern.ReturnOps (hoistSextLocal match? dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistSextLocal match? dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistSextLocal match? dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistSextLocal match? dst dprops)} :
    LocalRewritePattern.PreservesSemantics (hoistSextLocal match? dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistSextLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ := hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `sext`s.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hSXSome : (matchSext dX ctx.raw).isSome := by
    cases hM : matchSext dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, xp⟩, hSX⟩ := Option.isSome_iff_exists.mp hSXSome
  rw [hSX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hSYSome : (matchSext dY ctx.raw).isSome := by
    cases hM : matchSext dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, yp⟩, hSY⟩ := Option.isSome_iff_exists.mp hSYSome
  rw [hSY] at hpattern
  simp only [] at hpattern
  -- Recover both `sext`s.
  obtain ⟨opTypeX, hwX, xv, hxVal, hv0SextIs, hxType, hDomX, hxIn, xNotOp⟩ :=
    sext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefX hSX
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨opTypeY, hwY, yv, hyVal, hv1SextIs, hyType, hDomY, hyIn, yNotOp⟩ :=
    sext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefY hSY
      (by rw [hOperands]; simp) hv1Type
  -- Width guards: `opTypeX = opTypeY = i32`, `opIntType = i64`.
  have hOpResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType := by
    rw [hOpResType]
  rw [hxType, hyType, hOpResTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hXW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hYW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  -- Collapse widths to the literals.
  obtain ⟨xw⟩ := opTypeX; simp only at hXW; subst hXW
  obtain ⟨yw⟩ := opTypeY; simp only at hYW; subst hYW
  obtain ⟨rw'⟩ := opIntType; simp only at hRW; subst hRW
  -- Pin `v0v`/`v1v` to the two sexts (both narrow at `i32`).
  obtain rfl : v0v = Data.LLVM.Int.sext xv 64 hwX := by
    have := hv0Val.symm.trans hv0SextIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.sext yv 64 hwY := by
    have := hv1Val.symm.trans hv1SextIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr` (`i32`), transported to `ctx₁`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  -- The result type `i64` as a `TypeAttr`, and `op`'s result in-bounds.
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpResAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hOpResTypeVal
  -- Peel the two creations (inner `dst x y : i32`, then `zext inner : i64`).
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ sextNewOp hSextNew hDomX₁ hDomX₂
  cleanupHpattern hpattern
  have hInnerNeSext : innerOp ≠ sextNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  have hOpResAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hOpRes0In]; exact hOpResAttr
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSextNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSextNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSextNew hInnerNeSext]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSextNew (operation := innerOp)
    rw [if_neg hInnerNeSext] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `zext inner`.
  have hSextNewType : sextNewOp.getOpType! ctx₂.raw = .llvm .sext := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSextNew (operation := sextNewOp)]
  have hSextNewOperands : sextNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSextNew (operation := sextNewOp)]
  have hSextNewProps : sextNewOp.getProperties! ctx₂.raw (.llvm .sext)
      = () := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSextNew (operation := sextNewOp)]
  have hSextNewResTypes : sextNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSextNew (operation := sextNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResAttr₁
  -- Read refined `x`/`y` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hSextNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  -- Replay the inner op (`i32`), then the `sext` (`i32 → i64`).
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (it := ⟨32⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁) (inBounds := by grind)
      (srcType := ⟨32⟩) (resType := ⟨64⟩)
      (f := fun c => Data.LLVM.Int.sext c 64 (by omega))
      (by intro blockOperands mem
          exact sext_interpretOp' 32 ⟨64⟩ (by omega) _ () _ blockOperands mem)
      hSextNewType hSextNewProps hSextNewOperands hSextNewResTypes hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (Data.LLVM.Int.sext (dfn xt yt) 64 (by omega))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (sext xv) (sext yv) ⊒ sext (dfn xv yv) ⊒ sext (dfn xt yt)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine xv yv _ hwX)
    (Data.LLVM.Int.sext_mono (dfn xv yv) (dfn xt yt) (by omega) (hMono xv xt yv yt hxRef hyRef))
theorem AndSextSext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistSextLocal (matchBinopNoProps matchAnd) .and ()) h h₂ h₃ h₄ :=
  hoistSextLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun x y _ hlt => Data.LLVM.Int.AndSextSext)

theorem OrSextSext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistSextLocal (matchBinopNoProps matchOr) .or { disjoint := false }) h h₂ h₃ h₄ :=
  hoistSextLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun x y po hlt => by simpa using Data.LLVM.Int.OrSextSext (d := po.disjoint))

theorem XorSextSext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistSextLocal (matchBinopNoProps matchXor) .xor ()) h h₂ h₃ h₄ :=
  hoistSextLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun x y _ hlt => Data.LLVM.Int.XorSextSext)

/-! ### select_of_zext

  `zext (select c t f) → select c (zext t) (zext f)`. `op` is the `zext`, whose operand is a
  defining `select c t f`. Recover the `select`'s value/facts via
  `matchSelect_getVar?_of_EquationLemmaAt`, then create `zext t`, `zext f`, and a `select` over them.
-/

set_option maxHeartbeats 1000000 in
/-- Semantic content of a defining `select c t f` reached through an operand `base` of `op`:
    recovers `c`/`t`/`f`'s values and `t`/`f`'s target-side facts, plus `base`'s value
    `select cv tv fv`. The `select` analogue of `matchAdd_getVar?_of_EquationLemmaAt`. -/
private theorem matchSelect_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base cond tv fv : ValuePtr} {selOp : OperationPtr} {valType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some selOp)
    (hSel : matchSelect selOp ctx.raw = some (cond, tv, fv))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType valType) :
    ∃ (cv : Data.LLVM.Int 1) (tvv fvv : Data.LLVM.Int valType.bitwidth),
      state.variables.getVar? cond = some (RuntimeValue.int 1 cv) ∧
      state.variables.getVar? tv = some (RuntimeValue.int valType.bitwidth tvv) ∧
      state.variables.getVar? fv = some (RuntimeValue.int valType.bitwidth fvv) ∧
      state.variables.getVar? base = some (RuntimeValue.int valType.bitwidth
        (Data.LLVM.Int.select cv tvv fvv)) ∧
      (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ ∧
      (tv.getType! ctx.raw).val = Attribute.integerType valType ∧
      (fv.getType! ctx.raw).val = Attribute.integerType valType ∧
      cond.dominatesIp (InsertPoint.before op) ctx ∧
      tv.dominatesIp (InsertPoint.before op) ctx ∧ fv.dominatesIp (InsertPoint.before op) ctx ∧
      cond.InBounds ctx.raw ∧ tv.InBounds ctx.raw ∧ fv.InBounds ctx.raw ∧
      cond ∉ op.getResults! ctx.raw ∧ tv ∉ op.getResults! ctx.raw ∧ fv ∉ op.getResults! ctx.raw := by
  obtain ⟨hSelType, hSelNumResults, hSelOperands⟩ := matchSelect_implies hSel
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hSelOpEq : basePtr.op = selOp := by simp [getDefiningOp] at hDef; grind
  subst hSelOpEq
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hSelOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hSelVerified : basePtr.op.Verified ctx hSelOpIn := by grind
  obtain ⟨-, -, ⟨i1ty, hCondTy, hCondBw⟩, hResEqT, hResEqF⟩ :=
    OperationPtr.Verified.llvm_select hSelVerified hSelType
  have hCondEq : cond = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hSelOperands]; rfl
  have hTvEq : tv = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hSelOperands]; rfl
  have hFvEq : fv = (basePtr.op.getOperands! ctx.raw)[2]! := by rw [hSelOperands]; rfl
  have hOperand0 : basePtr.op.getOperand! ctx.raw 0 = cond := by
    rw [hCondEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : basePtr.op.getOperand! ctx.raw 1 = tv := by
    rw [hTvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : basePtr.op.getOperand! ctx.raw 2 = fv := by
    rw [hFvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- `base`'s type is the `select`'s result type (`valType`), which equals both value operands'.
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := i1ty; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTvType : (tv.getType! ctx.raw).val = Attribute.integerType valType := by
    rw [← hOperand1, ← hResEqT, ← hBaseTypeEq, hBaseType]
  have hFvType : (fv.getType! ctx.raw).val = Attribute.integerType valType := by
    rw [← hOperand2, ← hResEqF, ← hBaseTypeEq, hBaseType]
  -- The `select` has been interpreted into `state`.
  have hSelDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hSelOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hSelSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hSelDefines hOperand
  have hSelDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hSelPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_select hSelType
  obtain ⟨cfS, hInterpSel⟩ := stateWf basePtr.op hSelOpIn hSelPure hSelDomIp
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, -, hBaseResVal, -⟩ :=
    matchSelectOp_interpretOp_unfold hSelOpIn hSelType hSelNumResults hSelOperands
      hCondType hTvType hFvType hInterpSel
  have hDomBefore : ∀ v, v ∈ basePtr.op.getOperands! ctx.raw →
      v.dominatesIp (InsertPoint.before op) ctx := fun v hv =>
    ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hSelOpIn hv) hSelSDom
  have hNotRes : ∀ v, v ∈ basePtr.op.getOperands! ctx.raw → v ∉ op.getResults! ctx.raw := fun v hv =>
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSelSDom) v hv
  refine ⟨cv, tvv, fvv, hcVal, htVal, hfVal, ?_, hCondType, hTvType, hFvType,
    hDomBefore _ (by rw [hSelOperands]; simp), hDomBefore _ (by rw [hSelOperands]; simp),
    hDomBefore _ (by rw [hSelOperands]; simp), ?_, ?_, ?_,
    hNotRes _ (by rw [hSelOperands]; simp), hNotRes _ (by rw [hSelOperands]; simp),
    hNotRes _ (by rw [hSelOperands]; simp)⟩
  · rw [hBaseEq, hBaseResVal]
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]

set_option maxHeartbeats 1000000 in
theorem select_of_zext_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps select_of_zext_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges select_of_zext_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds select_of_zext_local}
    {h₄ : LocalRewritePattern.ReturnValues select_of_zext_local} :
    LocalRewritePattern.PreservesSemantics select_of_zext_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, select_of_zext_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchZext` (op is the zext).
  have hMatchSome : (matchZext op ctx.raw).isSome := by
    cases hM : matchZext op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, zp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hZProps⟩ := matchZext_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op` (the zext): operand `v0` and result share a widening relation.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opType, retType, hV0TypeV, hResTypeV, hwV⟩ :=
    OperationPtr.Verified.llvm_zext opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hV0Type : (v0.getType! ctx.raw).val = Attribute.integerType opType := by
    have := hV0TypeV; rw [hOperand0] at this; rw [this]
  have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType retType := by
    rw [hResTypeV]
  -- Peel the defining `select`.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dS, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSelSome : (matchSelect dS ctx.raw).isSome := by
    cases hM : matchSelect dS ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tv, fv⟩, hSel⟩ := Option.isSome_iff_exists.mp hSelSome
  rw [hSel] at hpattern
  simp only [] at hpattern
  -- Recover the `select`'s value and `t`/`f`'s facts.
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, hv0SelIs, hCondType, hTvType, hFvType, hDomC, hDomT,
      hDomF, hCIn, hTIn, hFIn, cNotOp, tNotOp, fNotOp⟩ :=
    matchSelect_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hSel
      (by rw [hOperands]; simp) hV0Type
  -- Unfold `op` (the zext) via the ext unfold, giving `op`'s result = `zext v0v`.
  obtain ⟨v0v, hv0Val, hMem, hOpResVal, hCf⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := .zext)
      (srcFn := fun a hw props => Data.LLVM.Int.zext a _ props.nneg hw)
      (props := zp)
      opInBounds hOpType hNumResults hOperands hZProps
      (show op.getResultTypes! ctx.raw = #[⟨.integerType retType, by grind⟩] by
        apply Array.ext
        · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
        · intro i h1 h2
          simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
          obtain rfl : i = 0 := by omega
          have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw)
            (index := 0) (by omega)
          grind)
      hwV zext_interpretOp' hinterp hV0Type
  subst hCf
  -- Pin `v0v = select cv tvv fvv` (both readings of `v0`'s value).
  obtain rfl : v0v = Data.LLVM.Int.select cv tvv fvv := by
    have := hv0Val.symm.trans hv0SelIs; simpa using this
  -- Width guards: `tv`'s type (`opType`) is `i32`, `op`'s result type (`retType`) is `i64`.
  rw [hTvType, hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hOW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  -- Collapse widths.
  obtain ⟨ow⟩ := opType; simp only at hOW; subst hOW
  obtain ⟨rw'⟩ := retType; simp only at hRW; subst hRW
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hOpResVal] at hsourceValues
  subst sourceValues
  -- Type attrs.
  have hOutTyAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hResType
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hOpResVal
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hTvTypeAttr : tv.getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, hTvType ▸ (tv.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hTvType
  have hCondTypeAttr : cond.getType! ctx.raw
      = (⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hCondType
  -- Peel the three creations (`zext tv`, `zext fv`, `select cond zt zf`).
  peelOpCreation!₂ hpattern ctx₁ ztOp hZt hDomT hDomT₁ hDomF hDomF₁
  have hDomC₁ : cond.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hZt
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomC
  peelOpCreation!₂ hpattern ctx₂ zfOp hZf hDomF₁ hDomF₂ hDomC₁ hDomC₂
  have hDomT₂ : tv.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hZf
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomT₁
  peelOpCreation!₂ hpattern ctx₃ selNewOp hSelNew hDomC₂ hDomC₃ hDomF₂ hDomF₃
  have hDomT₃ : tv.dominatesIp (InsertPoint.before op) ctx₃ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hSelNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomT₂
  cleanupHpattern hpattern
  have hZtNeZf : ztOp ≠ zfOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hZtNeSel : ztOp ≠ selNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hZfNeSel : zfOp ≠ selNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- Transports.
  have hOutTyAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hZt hOpRes0In]; exact hOutTyAttr
  have hOutTyAttr₂ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hZf
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hZt hOpRes0In)]
    exact hOutTyAttr₁
  -- Structural facts for `zext tv`.
  have hZtType : ztOp.getOpType! ctx₃.raw = .llvm .zext := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hZt (operation := ztOp),
      OperationPtr.getOpType!_WfRewriter_createOp hZf (operation := ztOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := ztOp)]
  have hZtOperands : ztOp.getOperands! ctx₃.raw = #[tv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hZt (operation := ztOp),
      OperationPtr.getOperands!_WfRewriter_createOp hZf (operation := ztOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := ztOp)]
  have hZtProps : ztOp.getProperties! ctx₃.raw (.llvm .zext) = zp := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hZt (operation := ztOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hZf hZtNeZf,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSelNew hZtNeSel]
  have hZtResTypes : ztOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hZt (operation := ztOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hZf (operation := ztOp)
    rw [if_neg hZtNeZf] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := ztOp)
    rw [if_neg hZtNeSel] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hOutTyAttr
  -- Structural facts for `zext fv`.
  have hZfType : zfOp.getOpType! ctx₃.raw = .llvm .zext := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hZf (operation := zfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := zfOp)]
  have hZfOperands : zfOp.getOperands! ctx₃.raw = #[fv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hZf (operation := zfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := zfOp)]
  have hZfProps : zfOp.getProperties! ctx₃.raw (.llvm .zext) = zp := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hZf (operation := zfOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSelNew hZfNeSel]
  have hZfResTypes : zfOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hZf (operation := zfOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := zfOp)
    rw [if_neg hZfNeSel] at hT3
    rw [hT3, hT]
    exact congrArg (fun t => #[t]) hOutTyAttr
  -- Structural facts for the `select`.
  have hSelNewType : selNewOp.getOpType! ctx₃.raw = .llvm .select := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewOperands : selNewOp.getOperands! ctx₃.raw
      = #[cond, ValuePtr.opResult (ztOp.getResult 0), ValuePtr.opResult (zfOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewNumResults : selNewOp.getNumResults! ctx₃.raw = 1 := by
    grind [OperationPtr.getNumResults!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewCondType : cond.getType! ctx₃.raw
      = (⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hSelNew
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hZf
          (WfRewriter.createOp_inBounds_mono (ptr := .value _) hZt hCIn)),
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hZf
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hZt hCIn),
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hZt hCIn]
    exact hCondTypeAttr
  -- Read refined `cond`/`tv`/`fv`.
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
      hDomC hDomC₃ cNotOp
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTIn htVal
      hDomT hDomT₃ tNotOp
  obtain ⟨ft, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFIn hfVal
      hDomF hDomF₃ fNotOp
  -- Replay the two `zext`s, then the `select`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_unaryInt_forward (state := state') (inBounds := by grind)
      (srcType := ⟨32⟩) (resType := ⟨64⟩)
      (f := fun c => Data.LLVM.Int.zext c 64 zp.nneg (by omega))
      (by intro blockOperands mem; exact zext_interpretOp' 32 ⟨64⟩ (by omega) _ zp _ blockOperands mem)
      hZtType hZtProps hZtOperands hZtResTypes hTVal'
  have hFVal₁ : s₁.variables.getVar? fv = some (RuntimeValue.int 32 ft) := by
    rw [hFrame₁ fv (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hFIn
      (WfRewriter.createOp_new_not_inBounds ztOp hZt))]
    exact hFVal'
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn
      (WfRewriter.createOp_new_not_inBounds ztOp hZt))]
    exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁) (inBounds := by grind)
      (srcType := ⟨32⟩) (resType := ⟨64⟩)
      (f := fun c => Data.LLVM.Int.zext c 64 zp.nneg (by omega))
      (by intro blockOperands mem; exact zext_interpretOp' 32 ⟨64⟩ (by omega) _ zp _ blockOperands mem)
      hZfType hZfProps hZfOperands hZfResTypes hFVal₁
  have hZtResIn₁ : (ValuePtr.opResult (ztOp.getResult 0)).InBounds ctx₁.raw := by
    have hnr : ztOp.getNumResults! ctx₁.raw = 1 := by
      grind [OperationPtr.getNumResults!_WfRewriter_createOp hZt (operation := ztOp)]
    clear valueRefinement state'Dom state'Wf hpattern
    rw [ValuePtr.inBounds_opResult]
    refine ⟨WfRewriter.createOp_new_inBounds ztOp hZt, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hZtRes₂ : s₂.variables.getVar? (ValuePtr.opResult (ztOp.getResult 0))
      = some (RuntimeValue.int 64 (Data.LLVM.Int.zext tt 64 zp.nneg (by omega))) := by
    rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hZtResIn₁
      (WfRewriter.createOp_new_not_inBounds zfOp hZf))]
    exact hRes₁
  have hCVal₂ : s₂.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₂ cond (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      (WfRewriter.createOp_inBounds_mono (ptr := .value cond) hZt hCIn)
      (WfRewriter.createOp_new_not_inBounds zfOp hZf))]
    exact hCVal₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_select_forward (state := s₂) (inBounds := by grind)
      (it := ⟨64⟩) hSelNewType hSelNewOperands
      (show selNewOp.getResultTypes! ctx₃.raw
          = #[(⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] by
        have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := selNewOp)
        rw [if_pos rfl] at hT; rw [hT]; exact congrArg (fun t => #[t]) hOutTyAttr)
      hCVal₂ hZtRes₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64 (Data.LLVM.Int.select ct
      (Data.LLVM.Int.zext tt 64 zp.nneg (by omega)) (Data.LLVM.Int.zext ft 64 zp.nneg (by omega)))],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `zext (select cv tvv fvv) ⊒ select cv (zext tvv) (zext fvv) ⊒ select ct (zext tt) (zext ft)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (Data.LLVM.Int.select_of_zext_rw (n := zp.nneg))
    (Data.LLVM.Int.select_mono _ _ _ _ _ _
      (Data.LLVM.Int.zext_mono tvv tt (by omega) htRef)
      (Data.LLVM.Int.zext_mono fvv ft (by omega) hfRef) hcRef)

/-! ### hoist_logic_op (`*TruncTrunc`)

  `(trunc X) outer (trunc Y) → trunc (X outer Y)` for `outer ∈ {and, or, xor}`, at `i64 → i32`. The
  narrowing mirror of the `*ZextZext` family: `op` is the outer op and *both* its operands are
  defining `trunc`s (recovered via `trunc_getVar?_of_EquationLemmaAt`). Create `inner = dst X Y`
  (`i64`) then `trunc inner` (`i32`).

  The created `trunc` always clears `nsw` and keeps `nuw` only for `and` (`useSndNuw`); see the flag
  discussion on `hoistTruncLocal` and the data lemmas in `LLVMProofs.lean`.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndTruncTrunc`/`OrTruncTrunc`/`XorTruncTrunc`. Parameterized over
    the outer op, the inner emitted op `dst`/`dfn` (`hSemDst`/`hMono`), whether the created `trunc`
    reuses the second `trunc`'s `nuw` (`useSndNuw`), and the refinement lemma `hRefine`. -/
theorem hoistTruncLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)} {useSndNuw : Bool}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (s0 u0 s1 u1 : Bool) (x y : Data.LLVM.Int 64) (po : propertiesOf (.llvm srcOp))
        (hgt : (32 : Nat) < 64),
        srcFn (Data.LLVM.Int.trunc x 32 s0 u0 hgt) (Data.LLVM.Int.trunc y 32 s1 u1 hgt) po
          ⊒ Data.LLVM.Int.trunc (dfn x y) 32 false (if useSndNuw then u1 else false) hgt)
    {h : LocalRewritePattern.ReturnOps (hoistTruncLocal match? dst dprops useSndNuw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistTruncLocal match? dst dprops useSndNuw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistTruncLocal match? dst dprops useSndNuw)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistTruncLocal match? dst dprops useSndNuw)} :
    LocalRewritePattern.PreservesSemantics (hoistTruncLocal match? dst dprops useSndNuw)
      h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistTruncLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ := hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `trunc`s.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hTXSome : (matchTrunc dX ctx.raw).isSome := by
    cases hM : matchTrunc dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, xp⟩, hTX⟩ := Option.isSome_iff_exists.mp hTXSome
  rw [hTX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hTYSome : (matchTrunc dY ctx.raw).isSome := by
    cases hM : matchTrunc dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, yp⟩, hTY⟩ := Option.isSome_iff_exists.mp hTYSome
  rw [hTY] at hpattern
  simp only [] at hpattern
  -- Recover both `trunc`s.
  obtain ⟨opTypeX, hwX, xv, hxVal, hv0TruncIs, hxType, hDomX, hxIn, xNotOp⟩ :=
    trunc_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefX hTX
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨opTypeY, hwY, yv, hyVal, hv1TruncIs, hyType, hDomY, hyIn, yNotOp⟩ :=
    trunc_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefY hTY
      (by rw [hOperands]; simp) hv1Type
  -- Width guards: `opTypeX = opTypeY = i64`, `opIntType = i32`.
  have hOpResTypeVal : ((op.getResult 0).get! ctx.raw).type.val
      = Attribute.integerType opIntType := by rw [hOpResType]
  rw [hxType, hyType, hOpResTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hXW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hYW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  -- Collapse widths to the literals.
  obtain ⟨xw⟩ := opTypeX; simp only at hXW; subst hXW
  obtain ⟨yw⟩ := opTypeY; simp only at hYW; subst hYW
  obtain ⟨rw'⟩ := opIntType; simp only at hRW; subst hRW
  -- Pin `v0v`/`v1v` to the two truncs (both wide at `i64`).
  obtain rfl : v0v = Data.LLVM.Int.trunc xv 32 xp.nsw xp.nuw hwX := by
    have := hv0Val.symm.trans hv0TruncIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.trunc yv 32 yp.nsw yp.nuw hwY := by
    have := hv1Val.symm.trans hv1TruncIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr` (`i64`), and the result type `i32` as a `TypeAttr`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpResAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hOpResTypeVal
  -- Peel the two creations (inner `dst x y : i64`, then `trunc inner : i32`).
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  peelOpCreation! hpattern ctx₂ truncNewOp hTruncNew hDomX₁ hDomX₂
  cleanupHpattern hpattern
  have hInnerNeTrunc : innerOp ≠ truncNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  have hOpResAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hOpRes0In]; exact hOpResAttr
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hTruncNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hTruncNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hTruncNew hInnerNeTrunc]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hTruncNew (operation := innerOp)
    rw [if_neg hInnerNeTrunc] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `trunc inner`.
  have hTruncNewType : truncNewOp.getOpType! ctx₂.raw = .llvm .trunc := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTruncNew (operation := truncNewOp)]
  have hTruncNewOperands : truncNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTruncNew (operation := truncNewOp)]
  have hTruncNewProps : truncNewOp.getProperties! ctx₂.raw (.llvm .trunc)
      = { nsw := false, nuw := if useSndNuw then yp.nuw else false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hTruncNew (operation := truncNewOp)]
  have hTruncNewResTypes : truncNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hTruncNew (operation := truncNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResAttr₁
  -- Read refined `x`/`y` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hTruncNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  -- Replay the inner op (`i64`), then the `trunc` (`i64 → i32`).
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (it := ⟨64⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁) (inBounds := by grind)
      (srcType := ⟨64⟩) (resType := ⟨32⟩)
      (f := fun c => Data.LLVM.Int.trunc c 32 false (if useSndNuw then yp.nuw else false) (by omega))
      (by intro blockOperands mem
          exact trunc_interpretOp' 64 ⟨32⟩ (by omega) _
            { nsw := false, nuw := if useSndNuw then yp.nuw else false } _ blockOperands mem)
      hTruncNewType hTruncNewProps hTruncNewOperands hTruncNewResTypes hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 32
      (Data.LLVM.Int.trunc (dfn xt yt) 32 false (if useSndNuw then yp.nuw else false) (by omega))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (trunc xv) (trunc yv) ⊒ trunc (dfn xv yv) ⊒ trunc (dfn xt yt)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine xp.nsw xp.nuw yp.nsw yp.nuw xv yv _ hwX)
    (Data.LLVM.Int.trunc_mono (dfn xv yv) (dfn xt yt) (by omega) (hMono xv xt yv yt hxRef hyRef))

theorem AndTruncTrunc_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistTruncLocal (matchBinopNoProps matchAnd) .and () true) h h₂ h₃ h₄ :=
  hoistTruncLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun s0 u0 s1 u1 x y _ hgt => by
      simpa using Data.LLVM.Int.AndTruncTrunc (s0 := s0) (u0 := u0) (s1 := s1) (u1 := u1))

theorem OrTruncTrunc_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistTruncLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) h h₂ h₃ h₄ :=
  hoistTruncLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun s0 u0 s1 u1 x y po hgt => by
      simpa using Data.LLVM.Int.OrTruncTrunc (s0 := s0) (u0 := u0) (s1 := s1) (u1 := u1)
        (d := po.disjoint))

theorem XorTruncTrunc_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistTruncLocal (matchBinopNoProps matchXor) .xor () false) h h₂ h₃ h₄ :=
  hoistTruncLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun s0 u0 s1 u1 x y _ hgt => by
      simpa using Data.LLVM.Int.XorTruncTrunc (s0 := s0) (u0 := u0) (s1 := s1) (u1 := u1))

/-! ### hoist_logic_op (`*AshrAshr`)

  `(X >>a Z) outer (Y >>a Z) → (X outer Y) >>a Z` for `outer ∈ {and, or, xor}`, arithmetic shift.
  `op` is the outer op; *both* its operands are the result of a defining `ashr _ Z` sharing the
  shift amount `Z`. Recover both `ashr`s via `matchBinop_getVar?_of_EquationLemmaAt` (`llvm.ashr`
  verifies via `verifyIntegerBinop`, so `Verified.llvm_ashr` gives `IsVerifiedIntegerBinop`), then
  create `inner = dst X Y` and `ashr inner Z`.
-/

/-- `llvm.ashr` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_ashr {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .ashr) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndAshrAshr`/`OrAshrAshr`/`XorAshrAshr`. Parameterized over the
    outer op (`srcOp`/`srcFn`/matcher-verifier-purity), the inner emitted op `dst` computing `dfn`
    (`hSemDst`), whether the created `ashr` keeps the second shift's `exact` (`useSndExact`), and the
    data-refinement lemma `hRefine`. -/
theorem hoistAshrLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)} {useSndExact : Bool}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ {w : Nat}, w = 64 → ∀ (xv yv zv : Data.LLVM.Int w) (e0 e1 : Bool)
        (po : propertiesOf (.llvm srcOp)),
        srcFn (Data.LLVM.Int.ashr xv zv e0) (Data.LLVM.Int.ashr yv zv e1) po
          ⊒ Data.LLVM.Int.ashr (dfn xv yv) zv (if useSndExact then e1 else false))
    {h : LocalRewritePattern.ReturnOps (hoistAshrLocal match? dst dprops useSndExact)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistAshrLocal match? dst dprops useSndExact)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistAshrLocal match? dst dprops useSndExact)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistAshrLocal match? dst dprops useSndExact)} :
    LocalRewritePattern.PreservesSemantics (hoistAshrLocal match? dst dprops useSndExact) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistAshrLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `ashr`s and the `z0 = z1` guard.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hAshrXSome : (matchAshr dX ctx.raw).isSome := by
    cases hM : matchAshr dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, z0, xashrp⟩, hAshrX⟩ := Option.isSome_iff_exists.mp hAshrXSome
  rw [hAshrX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hAshrYSome : (matchAshr dY ctx.raw).isSome := by
    cases hM : matchAshr dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, z1, yashrp⟩, hAshrY⟩ := Option.isSome_iff_exists.mp hAshrYSome
  rw [hAshrY] at hpattern
  simp only [] at hpattern
  have hZEq : z0 = z1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hZEq] at hpattern
  -- The matched props are the defining ops' properties.
  obtain ⟨-, -, -, hXPropsEq⟩ := matchAshr_implies hAshrX
  obtain ⟨-, -, -, hYPropsEq⟩ := matchAshr_implies hAshrY
  -- Recover both defining `ashr`s.  Their `exact` flags are `xashrp.exact`/`yashrp.exact`.
  obtain ⟨xv, z0v, hxVal, hz0Val, hv0AshrIs, hxType, hz0Type, hDomX, hDomZ0, hxIn, hz0In,
      xNotOp, z0NotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .ashr)
      (srcFn := fun a b p => Data.LLVM.Int.ashr a b p.exact)
      (matchBinopNoProps_implies matchAshr_implies)
      OperationPtr.Verified.llvm_ashr OperationPtr.Pure.llvm_ashr
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDefX
      (show matchBinopNoProps matchAshr dX ctx.raw = some (x, z0) by
        simp only [matchBinopNoProps, bind, Option.bind, hAshrX])
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨yv, z1v, hyVal, hz1Val, hv1AshrIs, hyType, hz1Type, hDomY, hDomZ1, hyIn, hz1In,
      yNotOp, z1NotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := .ashr)
      (srcFn := fun a b p => Data.LLVM.Int.ashr a b p.exact)
      (matchBinopNoProps_implies matchAshr_implies)
      OperationPtr.Verified.llvm_ashr OperationPtr.Pure.llvm_ashr
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDefY
      (show matchBinopNoProps matchAshr dY ctx.raw = some (y, z1) by
        simp only [matchBinopNoProps, bind, Option.bind, hAshrY])
      (by rw [hOperands]; simp) hv1Type
  -- Rewrite the recovered values' `exact` flags to the matched properties.
  rw [← hXPropsEq] at hv0AshrIs
  rw [← hYPropsEq] at hv1AshrIs
  -- `z0 = z1`, so `z0v = z1v`; pin `v0v`/`v1v`.
  have hzvEq : z1v = z0v := by
    have := hz1Val.symm.trans (hZEq ▸ hz0Val); simpa using this
  obtain rfl : v0v = Data.LLVM.Int.ashr xv z0v xashrp.exact := by
    have := hv0Val.symm.trans hv0AshrIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.ashr yv z1v yashrp.exact := by
    have := hv1Val.symm.trans hv1AshrIs; simpa using this
  rw [hzvEq] at hRes
  -- Width guard on `x`'s type (must be `i64`).  The initial `simp` swaps `≠ 64` to `= 64`, so the
  -- bail is the `isFalse` branch.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hWidth
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr`, transported to `ctx₁`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  -- Peel the two creations (inner `dst x y`, then `ashr inner z0`), transporting `x`/`y`/`z0`.
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  -- `z0` dominance through the first creation.
  have hDomZ0₁ : z0.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hInner
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomZ0
  peelOpCreation!₂ hpattern ctx₂ ashrNewOp hAshrNew hDomX₁ hDomX₂ hDomZ0₁ hDomZ0₂
  cleanupHpattern hpattern
  have hInnerNeAshr : innerOp ≠ ashrNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAshrNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAshrNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAshrNew hInnerNeAshr]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hAshrNew (operation := innerOp)
    rw [if_neg hInnerNeAshr] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `ashr inner z0`.
  have hAshrNewType : ashrNewOp.getOpType! ctx₂.raw = .llvm .ashr := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAshrNew (operation := ashrNewOp)]
  have hAshrNewOperands : ashrNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0), z0] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAshrNew (operation := ashrNewOp)]
  have hAshrNewProps : ashrNewOp.getProperties! ctx₂.raw (.llvm .ashr)
      = { exact := if useSndExact then yashrp.exact else false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAshrNew (operation := ashrNewOp)]
  have hAshrNewResTypes : ashrNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType opIntType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAshrNew (operation := ashrNewOp)
    rw [if_pos rfl] at hT
    rw [hT, hXGet₁]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Read refined `x`/`y`/`z0` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hAshrNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  obtain ⟨z0t, hZ0Val', hz0Ref⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hz0In hz0Val
      hDomZ0 hDomZ0₂ z0NotOp
  -- Replay the inner op, then the `ashr`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  have hZ0Res₁ : s₁.variables.getVar? z0 = some (RuntimeValue.int opIntType.bitwidth z0t) := by
    rw [hFrame₁ z0 (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      hz0In (WfRewriter.createOp_new_not_inBounds innerOp hInner))]
    exact hZ0Val'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.ashr a b (if useSndExact then yashrp.exact else false))
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAshrNewType hAshrNewProps hAshrNewOperands hAshrNewResTypes hRes₁ hZ0Res₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntType.bitwidth
      (Data.LLVM.Int.ashr (dfn xt yt) z0t (if useSndExact then yashrp.exact else false))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (ashr xv zv e0) (ashr yv zv e1) ⊒ ashr (dfn xv yv) zv eOut`
  --   `⊒ ashr (dfn xt yt) z0t eOut`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hWidth xv yv z0v xashrp.exact yashrp.exact _)
    (Data.LLVM.Int.ashr_mono (dfn xv yv) z0v (dfn xt yt) z0t (hMono xv xt yv yt hxRef hyRef) hz0Ref
      (if useSndExact then yashrp.exact else false))

theorem AndAshrAshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAshrLocal (matchBinopNoProps matchAnd) .and () true) h h₂ h₃ h₄ :=
  hoistAshrLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun hw x y z e0 e1 _ => by subst hw; exact Data.LLVM.Int.AndAshrAshr)

theorem OrAshrAshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAshrLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) h h₂ h₃ h₄ :=
  hoistAshrLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun hw x y z e0 e1 po => by subst hw; exact Data.LLVM.Int.OrAshrAshr (d := po.disjoint))

theorem XorAshrAshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistAshrLocal (matchBinopNoProps matchXor) .xor () false) h h₂ h₃ h₄ :=
  hoistAshrLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun hw x y z e0 e1 _ => by subst hw; exact Data.LLVM.Int.XorAshrAshr)

/-! ### hoist_logic_op (`*LshrLshr`)

  `(X >>l Z) outer (Y >>l Z) → (X outer Y) >>l Z` for `outer ∈ {and, or, xor}` (logical shift). `op`
  is the outer op; *both* its operands are defining `lshr _ Z` sharing the shift amount `Z`. Unlike
  `*AndAnd`, the defining ops verify only as `LLVMShift`, so their runtime value is recovered with
  the dedicated graph lemma `matchLshr_getVar?_of_EquationLemmaAt` (the arbitrary-shift-amount
  generalization of `lshrConst_getVar?_of_EquationLemmaAt`). Create `inner = dst X Y` then
  `lshr inner Z`.
-/

set_option maxHeartbeats 1000000 in
/-- Graph lemma for a value `base` defined by a *logical* shift `lshr X Z` (arbitrary shift amount
    `Z`, not necessarily constant). In a source state satisfying `EquationLemmaAt` before `op`,
    `base`'s runtime value is `lshr xv (sv transported to `X`'s width) exact`, and both `X`'s and
    the shift amount `Z`'s facts (value, type, dominance, in-bounds, not-a-result) are recovered.
    The generalization of `lshrConst_getVar?_of_EquationLemmaAt` to an arbitrary shift `ValuePtr`:
    the inner op verifies only as `LLVMShift`, so the operand-width equality is recovered
    dynamically via `matchShiftOp_interpretOp_unfold`. -/
theorem matchLshr_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x shamt : ValuePtr} {shrOp : OperationPtr}
    {shProps : propertiesOf (.llvm .lshr)} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some shrOp)
    (hLshr : matchLshr shrOp ctx.raw = some (x, shamt, shProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ (shType : IntegerType) (xv : Data.LLVM.Int intType.bitwidth)
      (sv : Data.LLVM.Int shType.bitwidth) (h' : shType.bitwidth = intType.bitwidth),
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? shamt = some (RuntimeValue.int shType.bitwidth sv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.lshr xv (h' ▸ sv) shProps.exact)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      (shamt.getType! ctx.raw).val = Attribute.integerType shType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      shamt.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧ shamt.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw ∧ shamt ∉ op.getResults! ctx.raw := by
  obtain ⟨lhsPtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hShrType, hShrNumResults, hShrOperands, hShProps⟩ := matchLshr_implies hLshr
  have hLhsIn : (ValuePtr.opResult lhsPtr).InBounds ctx.raw := by grind
  have hShrOpIn : lhsPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hlhsIdx : lhsPtr.index < lhsPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hlhsEq : lhsPtr = lhsPtr.op.getResult 0 := by
    have hidx : lhsPtr.index = 0 := by omega
    cases lhsPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hShrVerified : lhsPtr.op.Verified ctx hShrOpIn := by grind
  obtain ⟨-, -, hShrResEqOp0, shType, hShrOp1Type⟩ :=
    OperationPtr.Verified.llvm_lshr hShrVerified hShrType
  have hVTypeEq : (ValuePtr.opResult lhsPtr).getType! ctx.raw
      = ((lhsPtr.op.getResult 0).get! ctx.raw).type := by rw [hlhsEq]; rfl
  have hxIdxEq : x = (lhsPtr.op.getOperands! ctx.raw)[0]! := by rw [hShrOperands]; rfl
  have hShamtIdxEq : shamt = (lhsPtr.op.getOperands! ctx.raw)[1]! := by rw [hShrOperands]; rfl
  have hShrOperand0 : lhsPtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hShrOperand1 : lhsPtr.op.getOperand! ctx.raw 1 = shamt := by
    rw [hShamtIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    have : ((lhsPtr.op.getResult 0).get! ctx.raw).type.val
        = ((lhsPtr.op.getOperand! ctx.raw 0).getType! ctx.raw).val := hShrResEqOp0
    rw [hShrOperand0] at this
    rw [← this, ← hVTypeEq]; exact hBaseType
  have hShamtType : (shamt.getType! ctx.raw).val = Attribute.integerType shType := by
    rw [← hShrOperand1]; exact hShrOp1Type
  have hShrDefines : (ValuePtr.opResult lhsPtr).getDefiningOp! ctx.raw = some lhsPtr.op := by
    have hOwner := (ctx.wellFormed.operations lhsPtr.op hShrOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShrSDom : lhsPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hShrDefines hOperand
  have hShrDomIp : lhsPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShrPure : lhsPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_lshr hShrType
  obtain ⟨cfS, hInterpShr⟩ := stateWf lhsPtr.op hShrOpIn hShrPure hShrDomIp
  obtain ⟨xv, sv, h', hxVal, hsVal, -, hShrResVal, -⟩ :=
    matchShiftOp_interpretOp_unfold (srcOp := .lshr)
      (shiftFn := fun a b props => Data.LLVM.Int.lshr a b props.exact)
      (props := lhsPtr.op.getProperties! ctx.raw (.llvm .lshr))
      hShrOpIn hShrType hShrNumResults hShrOperands rfl
      (by intro bw bw' a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · rename_i hbw; obtain rfl : bw' = bw := by omega
            refine ⟨rfl, ?_⟩
            simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hInterpShr hxType hShamtType
  refine ⟨shType, xv, sv, h', hxVal, hsVal, ?_, hxType, hShamtType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hShProps, hlhsEq]; exact hShrResVal
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShrOpIn (by grind [OperationPtr.getOperands!])) hShrSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShrOpIn (by grind [OperationPtr.getOperands!])) hShrSDom
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShrSDom) x
      (by grind [OperationPtr.getOperands!])
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShrSDom) shamt
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndLshrLshr`/`OrLshrLshr`/`XorLshrLshr`. Parameterized over the
    outer op (`srcOp`/`srcFn`/matcher-verifier-purity), the inner emitted op `dst` computing `dfn`
    (`hSemDst`/`hMono`), whether the created `lshr` keeps the second shift's `exact` (`useSndExact`),
    and the data-refinement lemma `hRefine`. -/
theorem hoistLshrLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)} {useSndExact : Bool}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (xv yv zv : Data.LLVM.Int 64)
        (px py : propertiesOf (.llvm .lshr)) (po : propertiesOf (.llvm srcOp)),
        srcFn (Data.LLVM.Int.lshr xv zv px.exact) (Data.LLVM.Int.lshr yv zv py.exact) po
          ⊒ Data.LLVM.Int.lshr (dfn xv yv) zv (if useSndExact then py.exact else false))
    {h : LocalRewritePattern.ReturnOps (hoistLshrLocal match? dst dprops useSndExact)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistLshrLocal match? dst dprops useSndExact)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistLshrLocal match? dst dprops useSndExact)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistLshrLocal match? dst dprops useSndExact)} :
    LocalRewritePattern.PreservesSemantics (hoistLshrLocal match? dst dprops useSndExact) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistLshrLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ := hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `lshr`s and the `z0 = z1` guard.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hLshrXSome : (matchLshr dX ctx.raw).isSome := by
    cases hM : matchLshr dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, z0, xp⟩, hLshrX⟩ := Option.isSome_iff_exists.mp hLshrXSome
  rw [hLshrX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hLshrYSome : (matchLshr dY ctx.raw).isSome := by
    cases hM : matchLshr dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, z1, yp⟩, hLshrY⟩ := Option.isSome_iff_exists.mp hLshrYSome
  rw [hLshrY] at hpattern
  simp only [] at hpattern
  have hZEq : z0 = z1 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hZEq] at hpattern
  subst hZEq
  -- Recover both defining `lshr`s.
  obtain ⟨shTypeX, xv, z0v, h'X, hxVal, hz0Val, hv0LshrIs, hxType, hz0Type, hDomX, hDomZ0,
      hxIn, hz0In, xNotOp, z0NotOp⟩ :=
    matchLshr_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefX hLshrX
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨shTypeY, yv, z0v', h'Y, hyVal, hz0Val', hv1LshrIs, hyType, hz0Type', hDomY, hDomZ0',
      hyIn, hz0In', yNotOp, z0NotOp'⟩ :=
    matchLshr_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefY hLshrY
      (by rw [hOperands]; simp) hv1Type
  -- Both defining shifts share `z0`, so their recovered shift types/values coincide.
  obtain rfl : shTypeX = shTypeY := by
    have := hz0Type.symm.trans hz0Type'; exact (Attribute.integerType.inj this)
  obtain rfl : z0v = z0v' := by
    have := hz0Val.symm.trans hz0Val'; simpa using this
  -- Pin `v0v`/`v1v` to the two shifts.
  obtain rfl : v0v = Data.LLVM.Int.lshr xv (h'X ▸ z0v) xp.exact := by
    have := hv0Val.symm.trans hv0LshrIs; simpa using this
  obtain rfl : v1v = Data.LLVM.Int.lshr yv (h'Y ▸ z0v) yp.exact := by
    have := hv1Val.symm.trans hv1LshrIs; simpa using this
  -- Width guards on `x`'s type and `z0`'s type.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hXW
  rw [hz0Type] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hZW
  -- Collapse both widths to the literal `64`.
  obtain ⟨ow⟩ := opIntType; simp only at hXW; subst hXW
  obtain ⟨sw⟩ := shTypeX; simp only at hZW; subst hZW
  -- Source value (the `h' ▸` transports are now along `64 = 64`, definitionally the identity).
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s type as `TypeAttr`.
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  -- Peel the two creations (inner `dst x y`, then `lshr inner z0`), transporting `x`/`y`/`z0`.
  peelOpCreation!₂ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁
  have hDomZ0₁ : z0.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hInner
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomZ0
  peelOpCreation!₂ hpattern ctx₂ lshrNewOp hLshrNew hDomX₁ hDomX₂ hDomZ0₁ hDomZ0₂
  cleanupHpattern hpattern
  have hInnerNeLshr : innerOp ≠ lshrNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hLshrNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hLshrNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hLshrNew hInnerNeLshr]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hLshrNew (operation := innerOp)
    rw [if_neg hInnerNeLshr] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `lshr inner z0`.
  have hLshrNewType : lshrNewOp.getOpType! ctx₂.raw = .llvm .lshr := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hLshrNew (operation := lshrNewOp)]
  have hLshrNewOperands : lshrNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0), z0] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLshrNew (operation := lshrNewOp)]
  have hLshrNewProps : lshrNewOp.getProperties! ctx₂.raw (.llvm .lshr)
      = { exact := if useSndExact then yp.exact else false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLshrNew (operation := lshrNewOp)]
  have hLshrNewResTypes : lshrNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hLshrNew (operation := lshrNewOp)
    rw [if_pos rfl] at hT
    rw [hT, hXGet₁]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Read refined `x`/`y`/`z0` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  have hDomY₂ : y.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hLshrNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomY₁
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  obtain ⟨z0t, hZ0Val', hz0Ref⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hz0In hz0Val
      hDomZ0 hDomZ0₂ z0NotOp
  -- Replay the inner op, then the `lshr`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (it := ⟨64⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  have hZ0Res₁ : s₁.variables.getVar? z0 = some (RuntimeValue.int 64 z0t) := by
    rw [hFrame₁ z0 (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      hz0In (WfRewriter.createOp_new_not_inBounds innerOp hInner))]
    exact hZ0Val'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (it := ⟨64⟩)
      (f := fun a b => Data.LLVM.Int.lshr a b (if useSndExact then yp.exact else false))
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hLshrNewType hLshrNewProps hLshrNewOperands hLshrNewResTypes hRes₁ hZ0Res₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (Data.LLVM.Int.lshr (dfn xt yt) z0t (if useSndExact then yp.exact else false))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (lshr xv z0v e0) (lshr yv z0v e1) ⊒ lshr (dfn xv yv) z0v ⊒ lshr (dfn xt yt) z0t`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine xv yv z0v xp yp _)
    (Data.LLVM.Int.lshr_mono _ _ _ _ (hMono xv xt yv yt hxRef hyRef) hz0Ref
      (if useSndExact then yp.exact else false))

theorem AndLshrLshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistLshrLocal (matchBinopNoProps matchAnd) .and () true) h h₂ h₃ h₄ :=
  hoistLshrLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun x y z px py _ => Data.LLVM.Int.AndLshrLshr)

theorem OrLshrLshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistLshrLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) h h₂ h₃ h₄ :=
  hoistLshrLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun x y z px py po => Data.LLVM.Int.OrLshrLshr)

theorem XorLshrLshr_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistLshrLocal (matchBinopNoProps matchXor) .xor () false) h h₂ h₃ h₄ :=
  hoistLshrLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun x y z px py _ => Data.LLVM.Int.XorLshrLshr)

/-! ### hoist_shl_shl (`(X << Z) outer (Y << Z) → (X outer Y) << Z`)

  The two operands of the outer `and`/`or`/`xor` are both defining `shl`s with the *same* shift
  amount `Z`. Unlike the `zext`/`sext` hoists, the defining op is a *shift*: `llvm.shl` verifies via
  `verifyLLVMShift`, yielding only `IsVerifiedLLVMShift` (which pins the result type to operand 0 but
  leaves operand 1 — the shift amount — merely *some* integer). The equality of the shift operand's
  width to the shifted operand's width is recovered *dynamically* from the successful source
  interpretation via `matchShiftOp_interpretOp_unfold`, exactly as `lshrConst_getVar?_of_EquationLemmaAt`
  does for `lshr`. -/

-- `OperationPtr.Pure.llvm_shl` lives in `CommonGraphLemmas.lean`, beside the other purity facts.

set_option maxHeartbeats 1000000 in
/-- Graph lemma for an operand `base` of `op` defined by a `shl x z`: in a source state satisfying
    `EquationLemmaAt` before `op`, `base`'s runtime value is `shl xv zv`, and both `x` and `z`'s facts
    (values, dominance, in-bounds, not-a-result) are recovered. Modelled on
    `matchBinop_getVar?_of_EquationLemmaAt`, but the inner op verifies as `LLVMShift`, so the
    operand-width equality is recovered dynamically via `matchShiftOp_interpretOp_unfold`. -/
private theorem matchShl_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x z : ValuePtr} {shlOp : OperationPtr}
    {shProps : propertiesOf (.llvm .shl)} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some shlOp)
    (hShl : matchShl shlOp ctx.raw = some (x, z, shProps))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv zv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? z = some (RuntimeValue.int intType.bitwidth zv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.shl xv zv shProps.nsw shProps.nuw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ z.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧ z.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw ∧ z ∉ op.getResults! ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hShlType, hShlNumResults, hShlOperands, hShProps⟩ := matchShl_implies hShl
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hShlOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hShlVerified : basePtr.op.Verified ctx hShlOpIn := by grind
  obtain ⟨-, -, hShlResEqOp0, intType2, hShlOp1Type⟩ :=
    OperationPtr.Verified.llvm_shl hShlVerified hShlType
  have hVTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hShlOperands]; rfl
  have hzIdxEq : z = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hShlOperands]; rfl
  have hShlOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hShlOperand1 : basePtr.op.getOperand! ctx.raw 1 = z := by
    rw [hzIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    have hh : ((basePtr.op.getResult 0).get! ctx.raw).type.val
        = ((basePtr.op.getOperand! ctx.raw 0).getType! ctx.raw).val := hShlResEqOp0
    rw [hShlOperand0] at hh
    rw [← hh, ← hVTypeEq]; exact hBaseType
  have hzValType : (z.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hShlOperand1, hShlOp1Type]
  have hShlDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hShlOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShlSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hShlDefines hOperand
  have hShlDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShlPure : basePtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_shl hShlType
  obtain ⟨cfS, hInterpShl⟩ := stateWf basePtr.op hShlOpIn hShlPure hShlDomIp
  obtain ⟨xv, zv, h', hxVal, hzVal, -, hShlResVal, -⟩ :=
    matchShiftOp_interpretOp_unfold (srcOp := .shl)
      (shiftFn := fun a b props => Data.LLVM.Int.shl a b props.nsw props.nuw)
      (props := basePtr.op.getProperties! ctx.raw (.llvm .shl))
      hShlOpIn hShlType hShlNumResults hShlOperands rfl
      (by intro bw bw' a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · rename_i hbw; obtain rfl : bw' = bw := by omega
            refine ⟨rfl, ?_⟩
            simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hInterpShl hxType hzValType
  obtain ⟨w⟩ := intType; obtain ⟨w2⟩ := intType2
  simp only at h' hxType hxVal hzVal hShlResVal ⊢; subst w2
  refine ⟨xv, zv, hxVal, hzVal, ?_, hxType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hShProps, hBaseEq]; exact hShlResVal
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShlOpIn (by grind [OperationPtr.getOperands!])) hShlSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShlOpIn (by grind [OperationPtr.getOperands!])) hShlSDom
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShlSDom) x
      (by grind [OperationPtr.getOperands!])
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShlSDom) z
      (by grind [OperationPtr.getOperands!])

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `AndShlShl`/`OrShlShl`/`XorShlShl`. Parameterized over the outer op
    `srcOp`/`srcFn`, the inner emitted op `dst`/`dfn` (`hSemDst`/`hMono`), whether the emitted `shl`
    keeps the second shift's `nuw` (`useSndNuw`), and the data refinement lemma `hRefine`. -/
theorem hoistShlLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)} {useSndNuw : Bool}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (s0 u0 s1 u1 : Bool) (xv yv zv : Data.LLVM.Int 64)
        (po : propertiesOf (.llvm srcOp)),
        srcFn (Data.LLVM.Int.shl xv zv s0 u0) (Data.LLVM.Int.shl yv zv s1 u1) po
          ⊒ Data.LLVM.Int.shl (dfn xv yv) zv false (if useSndNuw then u1 else false))
    {h : LocalRewritePattern.ReturnOps (hoistShlLocal match? dst dprops useSndNuw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (hoistShlLocal match? dst dprops useSndNuw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (hoistShlLocal match? dst dprops useSndNuw)}
    {h₄ : LocalRewritePattern.ReturnValues (hoistShlLocal match? dst dprops useSndNuw)} :
    LocalRewritePattern.PreservesSemantics (hoistShlLocal match? dst dprops useSndNuw) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, hoistShlLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, v1⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ := hVerified opVerif hOpType
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hv1Eq : v1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = v1 := by
    rw [hv1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (v0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (v1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer op's interpretation.
  obtain ⟨v0v, v1v, hv0Val, hv1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  -- Peel the two defining `shl`s.
  have hDefXSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dX, hDefX⟩ := Option.isSome_iff_exists.mp hDefXSome
  rw [hDefX] at hpattern
  simp only [] at hpattern
  have hShlXSome : (matchShl dX ctx.raw).isSome := by
    cases hM : matchShl dX ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, z0, p0⟩, hShlX⟩ := Option.isSome_iff_exists.mp hShlXSome
  rw [hShlX] at hpattern
  simp only [] at hpattern
  have hDefYSome : (getDefiningOp v1 ctx.raw).isSome := by
    cases hM : getDefiningOp v1 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dY, hDefY⟩ := Option.isSome_iff_exists.mp hDefYSome
  rw [hDefY] at hpattern
  simp only [] at hpattern
  have hShlYSome : (matchShl dY ctx.raw).isSome := by
    cases hM : matchShl dY ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨y, z1, p1⟩, hShlY⟩ := Option.isSome_iff_exists.mp hShlYSome
  rw [hShlY] at hpattern
  simp only [] at hpattern
  -- The `z0 != z1` guard (`simp` swaps it to `if z0 = z1 then continue else bail`).
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hZeq
  -- Recover both `shl`s.
  obtain ⟨xv, zv0, hxVal, hz0Val, hv0ShlIs, hxType, hDomX, hDomZ, hxIn, hz0In, xNotOp, z0NotOp⟩ :=
    matchShl_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefX hShlX
      (by rw [hOperands]; simp) hv0Type
  obtain ⟨yv, zv1, hyVal, hz1Val, hv1ShlIs, hyType, hDomY, hDomZ1, hyIn, hz1In, yNotOp, z1NotOp⟩ :=
    matchShl_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefY hShlY
      (by rw [hOperands]; simp) hv1Type
  -- Width guards: `opIntType = i64`.
  have hOpResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType := by
    rw [hOpResType]
  rw [hxType, hyType, hOpResTypeVal] at hpattern
  simp only [] at hpattern
  -- All three width guards share the condition `opIntType.bitwidth = 64`, so one `split` closes all.
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hW1
  -- Collapse the width to `64`.
  obtain ⟨bw⟩ := opIntType
  simp only at hW1 hxType hyType hxVal hyVal hz0Val hz1Val hv0ShlIs hv1ShlIs hRes ⊢
  subst hW1
  -- The two shift amounts share a value.
  obtain rfl : zv0 = zv1 := by
    have hh : (some (RuntimeValue.int 64 zv0) : Option RuntimeValue) = some (RuntimeValue.int 64 zv1) := by
      rw [← hz0Val, hZeq, hz1Val]
    simpa using hh
  -- Pin `v0v`/`v1v` to the two shifts.
  obtain rfl : v0v = Data.LLVM.Int.shl xv zv0 p0.nsw p0.nuw := by
    have hh := hv0Val.symm.trans hv0ShlIs; simpa using hh
  obtain rfl : v1v = Data.LLVM.Int.shl yv zv0 p1.nsw p1.nuw := by
    have hh := hv1Val.symm.trans hv1ShlIs; simpa using hh
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- `x`'s / `op`'s result types as `TypeAttr` (`i64`).
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpResAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hOpResTypeVal
  -- Peel the two creations (inner `dst x y`, then `shl inner z0`).
  peelOpCreation!₃ hpattern ctx₁ innerOp hInner hDomX hDomX₁ hDomY hDomY₁ hDomZ hDomZ₁
  peelOpCreation!₃ hpattern ctx₂ shlNewOp hShlNew hDomX₁ hDomX₂ hDomY₁ hDomY₂ hDomZ₁ hDomZ₂
  cleanupHpattern hpattern
  have hInnerNeShl : innerOp ≠ shlNewOp := by
    clear hpattern state'Wf state'Dom valueRefinement; grind
  have hXGet₁ : x.getType! ctx₁.raw = x.getType! ctx.raw :=
    ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hxIn
  have hOpResAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hInner hOpRes0In]; exact hOpResAttr
  -- Structural facts: the inner `dst x y`.
  have hInnerType : innerOp.getOpType! ctx₂.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOpType!_WfRewriter_createOp hShlNew (operation := innerOp)]
  have hInnerOperands : innerOp.getOperands! ctx₂.raw = #[x, y] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getOperands!_WfRewriter_createOp hShlNew (operation := innerOp)]
  have hInnerProps : innerOp.getProperties! ctx₂.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hInner (operation := innerOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hShlNew hInnerNeShl]
  have hInnerResTypes : innerOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hInner (operation := innerOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hShlNew (operation := innerOp)
    rw [if_neg hInnerNeShl] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hXTypeAttr
  -- Structural facts: the outer `shl inner z0`.
  have hShlNewType : shlNewOp.getOpType! ctx₂.raw = .llvm .shl := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hShlNew (operation := shlNewOp)]
  have hShlNewOperands : shlNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (innerOp.getResult 0), z0] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hShlNew (operation := shlNewOp)]
  have hShlNewProps : shlNewOp.getProperties! ctx₂.raw (.llvm .shl)
      = { nsw := false, nuw := if useSndNuw then p1.nuw else false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hShlNew (operation := shlNewOp)]
  have hShlNewResTypes : shlNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType ⟨64⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hShlNew (operation := shlNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResAttr₁
  -- Read refined `x`/`y`/`z0` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  obtain ⟨yt, hYVal', hyRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hyIn hyVal
      hDomY hDomY₂ yNotOp
  obtain ⟨zt, hZVal', hzRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hz0In hz0Val
      hDomZ hDomZ₂ z0NotOp
  -- Replay the inner op, then the outer `shl`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (it := ⟨64⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hInnerType hInnerProps hInnerOperands hInnerResTypes hXVal' hYVal'
  have hZRes₁ : s₁.variables.getVar? z0 = some (RuntimeValue.int 64 zt) := by
    rw [hFrame₁ z0 (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hz0In
      (WfRewriter.createOp_new_not_inBounds innerOp hInner))]
    exact hZVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (it := ⟨64⟩)
      (f := fun a b => Data.LLVM.Int.shl a b false (if useSndNuw then p1.nuw else false))
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hShlNewType hShlNewProps hShlNewOperands hShlNewResTypes hRes₁ hZRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (Data.LLVM.Int.shl (dfn xt yt) zt false (if useSndNuw then p1.nuw else false))],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble via the data lemma and monotonicity.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans
    (hRefine p0.nsw p0.nuw p1.nsw p1.nuw xv yv zv0 (op.getProperties! ctx.raw (.llvm srcOp)))
    (Data.LLVM.Int.shl_mono (dfn xv yv) zv0 (dfn xt yt) zt (hMono xv xt yv yt hxRef hyRef) hzRef
      false (if useSndNuw then p1.nuw else false))

theorem AndShlShl_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistShlLocal (matchBinopNoProps matchAnd) .and () true) h h₂ h₃ h₄ :=
  hoistShlLocal_preservesSemantics (srcOp := .and) (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b) (dfn := fun a b => Data.LLVM.Int.and a b)
    (matchBinopNoProps_implies matchAnd_implies) OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.and_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun _ _ _ _ _ _ _ _ => by simpa using Data.LLVM.Int.AndShlShl)

theorem OrShlShl_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistShlLocal (matchBinopNoProps matchOr) .or { disjoint := false } false) h h₂ h₃ h₄ :=
  hoistShlLocal_preservesSemantics (srcOp := .or) (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    (dfn := fun a b => Data.LLVM.Int.or a b false)
    (matchBinopNoProps_implies matchOr_implies) OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.or_mono a₁ b₁ a₂ b₂ false h₁ h₂)
    (fun _ _ _ _ _ _ _ po => by simpa using Data.LLVM.Int.OrShlShl (d := po.disjoint))

theorem XorShlShl_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (hoistShlLocal (matchBinopNoProps matchXor) .xor () false) h h₂ h₃ h₄ :=
  hoistShlLocal_preservesSemantics (srcOp := .xor) (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b) (dfn := fun a b => Data.LLVM.Int.xor a b)
    (matchBinopNoProps_implies matchXor_implies) OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ b₁ a₂ b₂ h₁ h₂)
    (fun _ _ _ _ _ _ _ _ => by simpa using Data.LLVM.Int.XorShlShl)

/-! ### commute_int_constant_to_rhs (`commute_const_*`)

  `(C op x) → (x op C)` for `op ∈ {add, mul, and, or, xor}`, where `C` is an integer constant and
  `x` is not, canonicalizing the constant to the right-hand side. `op` is a binop matched directly;
  the emitted op is the *same* opcode with its two operands swapped, carrying the *same* properties
  (each op — including its overflow/`disjoint` flags — is commutative, so nothing needs clearing).
  Width-generic. -/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the five `commute_const_*` combines. Parameterized over the binop
    opcode `dst`/`match?`, its interpretation `srcFn` (`hSemSrc`), commutativity `hComm` (an
    equality — the flags are symmetric under commutation), and monotonicity `hMono`. The two
    constant guards on `lhs`/`rhs` are irrelevant to correctness (commuting is always sound); they
    are only peeled. -/
theorem commuteConstLocal_preservesSemantics {dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm dst) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode →
      Option (ValuePtr × ValuePtr × propertiesOf (.llvm dst))}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r p},
        match? opp c = some (l, r, p) →
        opp.getOpType! c = .llvm dst ∧ opp.getNumResults! c = 1 ∧
          opp.getOperands! c = #[l, r] ∧ p = opp.getProperties! c (.llvm dst))
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm dst → opp.IsVerifiedIntegerBinop c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm dst))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' dst props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hComm : ∀ {bw : Nat} (a b : Data.LLVM.Int bw) (p : propertiesOf (.llvm dst)),
        srcFn a b p = srcFn b a p)
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw) (p : propertiesOf (.llvm dst)),
        a₁ ⊒ b₁ → a₂ ⊒ b₂ → srcFn a₁ a₂ p ⊒ srcFn b₁ b₂ p)
    {h : LocalRewritePattern.ReturnOps (commuteConstLocal dst match?)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (commuteConstLocal dst match?)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (commuteConstLocal dst match?)}
    {h₄ : LocalRewritePattern.ReturnValues (commuteConstLocal dst match?)} :
    LocalRewritePattern.PreservesSemantics (commuteConstLocal dst match?) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, commuteConstLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `match?`.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, props⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the constant guards: `lhs` must be a constant, `rhs` must not.
  have hCstLhsSome : (matchConstantIntVal lhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal lhs ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨clhs, hCstLhs⟩ := Option.isSome_iff_exists.mp hCstLhsSome
  rw [hCstLhs] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hCstRhs
  -- Verifier facts for `op`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    hVerified opVerif hOpType
  have hlhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hrhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hlhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hrhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hlhsType : (lhs.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hrhsType : (rhs.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the source binop.
  obtain ⟨lhsv, rhsv, hlhsVal, hrhsVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := dst) (srcFn := srcFn) (props := props)
      opInBounds hOpType hNumResults hOperands hProps
      (by intro bw a b props' resultTypes blockOperands mem res hh
          rw [hSemSrc bw a b props' resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hlhsType hrhsType
  subst hCf
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Dominance / freshness for the two operands.
  have hDomL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hLIn : lhs.InBounds ctx.raw := by grind
  have hRIn : rhs.InBounds ctx.raw := by grind
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the single op creation (`dst rhs lhs`), transporting `lhs`'s dominance.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomL hDomL₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[rhs, lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.llvm dst) = props := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hOpResVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType :=
    congrArg Subtype.val hOpResType
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType opIntType,
          hOpResVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) (Subtype.ext hOpResVal)
  have hDomR₁ : rhs.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomR
  -- Read both refined operands in the target state.
  obtain ⟨lt, hLVal', hlRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLIn hlhsVal
      hDomL hDomL₁ lNotOp
  obtain ⟨rt, hRVal', hrRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRIn hrhsVal
      hDomR hDomR₁ rNotOp
  -- Replay the created (swapped) op forward: operands `#[rhs, lhs]` give `srcFn rt lt props`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := state') (inBounds := by grind)
      (f := fun a b => srcFn a b props)
      (by intro resultTypes blockOperands mem; exact hSemSrc _ _ _ props _ _ _)
      hNewType hNewProps hNewOperands hNewResTypes hRVal' hLVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntType.bitwidth (srcFn rt lt props)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- `srcFn lhsv rhsv props ⊒ srcFn rt lt props` by commutativity then monotonicity.
  simp only [Data.LLVM.Int.cast_self]
  rw [hComm lhsv rhsv props]
  exact hMono rhsv lhsv rt lt props hrRef hlRef

theorem commute_const_add_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (commuteConstLocal .add matchAdd) h h₂ h₃ h₄ :=
  commuteConstLocal_preservesSemantics (dst := .add)
    (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
    matchAdd_implies OperationPtr.Verified.llvm_add
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a b p => Data.LLVM.Int.add_comm_flags a b)
    (fun a₁ a₂ b₁ b₂ p h₁ h₂ => Data.LLVM.Int.add_mono a₁ a₂ b₁ b₂ h₁ h₂ p.nsw p.nuw)

theorem commute_const_mul_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (commuteConstLocal .mul matchMul) h h₂ h₃ h₄ :=
  commuteConstLocal_preservesSemantics (dst := .mul)
    (srcFn := fun a b p => Data.LLVM.Int.mul a b p.nsw p.nuw)
    matchMul_implies OperationPtr.Verified.llvm_mul
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a b p => Data.LLVM.Int.mul_comm a b)
    (fun a₁ a₂ b₁ b₂ p h₁ h₂ => Data.LLVM.Int.mul_mono a₁ a₂ b₁ b₂ h₁ h₂ p.nsw p.nuw)

theorem commute_const_and_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (commuteConstLocal .and matchAnd) h h₂ h₃ h₄ :=
  commuteConstLocal_preservesSemantics (dst := .and)
    (srcFn := fun a b _ => Data.LLVM.Int.and a b)
    matchAnd_implies OperationPtr.Verified.llvm_and
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a b _ => Data.LLVM.Int.and_comm a b)
    (fun a₁ a₂ b₁ b₂ _ h₁ h₂ => Data.LLVM.Int.and_mono a₁ a₂ b₁ b₂ h₁ h₂)

theorem commute_const_or_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (commuteConstLocal .or matchOr) h h₂ h₃ h₄ :=
  commuteConstLocal_preservesSemantics (dst := .or)
    (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
    matchOr_implies OperationPtr.Verified.llvm_or
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a b p => Data.LLVM.Int.or_comm a b)
    (fun a₁ a₂ b₁ b₂ p h₁ h₂ => Data.LLVM.Int.or_mono a₁ a₂ b₁ b₂ p.disjoint h₁ h₂)

theorem commute_const_xor_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (commuteConstLocal .xor matchXor) h h₂ h₃ h₄ :=
  commuteConstLocal_preservesSemantics (dst := .xor)
    (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
    matchXor_implies OperationPtr.Verified.llvm_xor
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a b _ => Data.LLVM.Int.xor_comm a b)
    (fun a₁ a₂ b₁ b₂ _ h₁ h₂ => Data.LLVM.Int.xor_mono a₁ a₂ b₁ b₂ h₁ h₂)

/-! ### binop_left_to_zero :  (0 op X)  →  0   for op ∈ {shl, lshr, ashr, mul}

  Graph-level `PreservesSemantics` for the four value-replacement combines that fold `OP (const 0) X`
  into the constant-zero operand itself. All four share one combinator proof
  (`binopZeroLeftLocal_preservesSemantics`), unfolding the source op with the width-recovering
  `matchShiftOp_interpretOp_unfold` (valid at every one of the four opcodes: `shl`/`lshr` verify via
  `verifyLLVMShift` directly, `mul`/`ashr` via `verifyIntegerBinop`, which is *stronger* and yields
  `IsVerifiedLLVMShift` through `isVerifiedLLVMShift_of_isVerifiedIntegerBinop`). The matched left
  operand's value is pinned to `constant _ 0` with `matchConstantIntVal_getVar?_of_EquationLemmaAt`;
  no operations are created, so the target-state reasoning collapses to reading the refined operand
  and one `isRefinedBy_trans` with the width-generic data lemma. -/

/-- `verifyIntegerBinop` guarantees strictly more than `verifyLLVMShift`, so its structural bundle
    can be weakened to the shift one (used for the `mul`/`ashr` instances, whose operands are pinned
    to a common integer type). -/
private theorem isVerifiedLLVMShift_of_isVerifiedIntegerBinop {ctx : WfIRContext OpCode}
    {op : OperationPtr} (h : op.IsVerifiedIntegerBinop ctx) : op.IsVerifiedLLVMShift ctx := by
  obtain ⟨hr, ho, _, _, it, hResT, hOp0, hOp1⟩ := h
  refine ⟨hr, ho, ?_, it, ?_⟩
  · rw [hResT, hOp0]
  · rw [hOp1]

/-- Shift-form `hSemSrc` for `llvm.shl`: the interpreter's own width guard forces the shift amount to
    have the operand's width, and the result is the shift value. -/
private theorem shl_zeroLeftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .shl)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .shl props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.shl x (h' ▸ y) props.nsw props.nuw)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- Shift-form `hSemSrc` for `llvm.lshr`. -/
private theorem lshr_zeroLeftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .lshr)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .lshr props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.lshr x (h' ▸ y) props.exact)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- Shift-form `hSemSrc` for `llvm.ashr`. -/
private theorem ashr_zeroLeftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .ashr)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .ashr props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.ashr x (h' ▸ y) props.exact)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

/-- Shift-form `hSemSrc` for `llvm.mul`. -/
private theorem mul_zeroLeftSem (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
    (props : propertiesOf (.llvm .mul)) (resultTypes : Array TypeAttr)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (h : Llvm.interpretOp' .mul props resultTypes #[.int bw x, .int bw' y] blockOperands mem
      = some (.ok res)) :
    ∃ (h' : bw' = bw),
      res = (#[.int bw (Data.LLVM.Int.mul x (h' ▸ y) props.nsw props.nuw)], mem, none) := by
  simp only [Llvm.interpretOp'] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hbw
    obtain rfl : bw' = bw := by omega
    refine ⟨rfl, ?_⟩
    simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at h
    grind

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the four `*_left_to_zero` combines. The source op is matched with
    `matchPair` (its own binary matcher), interpreted with `matchShiftOp_interpretOp_unfold` via the
    shift-form `hSemSrc`, and its left operand is pinned to `constant _ 0`; no operations are
    created, so the result is replaced by that constant-zero operand and the obligation reduces to
    the width-generic data lemma `hRefine`. -/
theorem binopZeroLeftLocal_preservesSemantics {srcOp : Llvm} {α : Type}
    {matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α)}
    {shiftFn : ∀ {bw : Nat},
      Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    (hMatchImplies : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs a},
        matchPair op ctx = some (lhs, rhs, a) →
        op.getOpType! ctx = .llvm srcOp ∧
        op.getNumResults! ctx = 1 ∧
        op.getOperands! ctx = #[lhs, rhs])
    (hVerified : ∀ {ctx : WfIRContext OpCode} {op : OperationPtr}
        {opInBounds : op.InBounds ctx.raw},
        op.Verified ctx opInBounds → op.getOpType! ctx.raw = .llvm srcOp →
        op.IsVerifiedLLVMShift ctx)
    (hSemSrc : ∀ (bw bw' : Nat) (x : Data.LLVM.Int bw) (y : Data.LLVM.Int bw')
        (props : propertiesOf (.llvm srcOp)) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw' y] blockOperands mem
          = some (.ok res) →
        ∃ (h' : bw' = bw), res = (#[.int bw (shiftFn x (h' ▸ y) props)], mem, none))
    (hRefine : ∀ {bw : Nat} (y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp)),
        shiftFn (Data.LLVM.Int.constant bw 0) y props ⊒ Data.LLVM.Int.constant bw 0)
    {h : LocalRewritePattern.ReturnOps (binopZeroLeftLocal matchPair)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (binopZeroLeftLocal matchPair)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (binopZeroLeftLocal matchPair)}
    {h₄ : LocalRewritePattern.ReturnValues (binopZeroLeftLocal matchPair)} :
    LocalRewritePattern.PreservesSemantics (binopZeroLeftLocal matchPair) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, binopZeroLeftLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the binary match.
  have hMatchSome : (matchPair op ctx.raw).isSome := by
    cases hM : matchPair op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨zero, rhs, aprops⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  -- Result-type guard: the result must be an integer.
  obtain ⟨intType, hResType⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Constant match on the left operand.
  have hCstSome : (matchConstantIntVal zero ctx.raw).isSome := by
    cases hM : matchConstantIntVal zero ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cst, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  -- The `value = 0` guard (the initial `simp` swapped the negated `if`).
  have hVal0 : cst.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hVal0] at hpattern
  -- Structural facts from the verifier.
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hResEqOp0, intType2, hOp1Type⟩ := hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = zero := by
    rw [show zero = (op.getOperands! ctx.raw)[0]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [show rhs = (op.getOperands! ctx.raw)[1]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hLhsType : (zero.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, ← hResEqOp0, hResType]
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2 := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the source interpretation.
  obtain ⟨x, y, h', hlVal, hrVal, hMem, hRes, hCf⟩ :=
    matchShiftOp_interpretOp_unfold (props := op.getProperties! ctx.raw (.llvm srcOp))
      opInBounds hOpType hNumResults hOperands rfl hSemSrc hinterp hLhsType hRhsType
  subst hCf
  -- Pin the left operand's runtime value to `constant _ 0`.
  have hzeroVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hLhsType
  have hxEq : x = Data.LLVM.Int.constant intType.bitwidth cst.value := by
    have := hlVal.symm.trans hzeroVal; simpa using this
  rw [hVal0] at hxEq
  subst hxEq
  -- The rewrite replaces `op`'s result with the (dominating, non-result) operand `zero`.
  have hDomZero : zero.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have zNotOp : ¬ zero ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Nothing is created: `newCtx = ctx`, `newOps = #[]`, `newValues = #[zero]`.
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[zero] := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hpattern; grind
  obtain ⟨zt, hZVal', hztRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
      hDomZero hDomZero zNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth zt], by simp [hZVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  refine isRefinedBy_trans ?_ hztRef
  simpa [Data.LLVM.Int.cast_self] using hRefine (h' ▸ y) _

theorem shl_left_to_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (binopZeroLeftLocal matchShl)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (binopZeroLeftLocal matchShl)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (binopZeroLeftLocal matchShl)}
    {h₄ : LocalRewritePattern.ReturnValues (binopZeroLeftLocal matchShl)} :
    LocalRewritePattern.PreservesSemantics (binopZeroLeftLocal matchShl) h h₂ h₃ h₄ :=
  binopZeroLeftLocal_preservesSemantics (srcOp := .shl)
    (shiftFn := fun x y props => Data.LLVM.Int.shl x y props.nsw props.nuw)
    (fun hm => ⟨(matchShl_implies hm).1, (matchShl_implies hm).2.1, (matchShl_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_shl shl_zeroLeftSem
    (fun _y props => Data.LLVM.Int.shl_zero_left (nsw := props.nsw) (nuw := props.nuw))

theorem lshr_left_to_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (binopZeroLeftLocal matchLshr)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (binopZeroLeftLocal matchLshr)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (binopZeroLeftLocal matchLshr)}
    {h₄ : LocalRewritePattern.ReturnValues (binopZeroLeftLocal matchLshr)} :
    LocalRewritePattern.PreservesSemantics (binopZeroLeftLocal matchLshr) h h₂ h₃ h₄ :=
  binopZeroLeftLocal_preservesSemantics (srcOp := .lshr)
    (shiftFn := fun x y props => Data.LLVM.Int.lshr x y props.exact)
    (fun hm => ⟨(matchLshr_implies hm).1, (matchLshr_implies hm).2.1, (matchLshr_implies hm).2.2.1⟩)
    OperationPtr.Verified.llvm_lshr lshr_zeroLeftSem
    (fun _y props => Data.LLVM.Int.lshr_zero_left (exact := props.exact))

theorem ashr_left_to_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (binopZeroLeftLocal matchAshr)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (binopZeroLeftLocal matchAshr)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (binopZeroLeftLocal matchAshr)}
    {h₄ : LocalRewritePattern.ReturnValues (binopZeroLeftLocal matchAshr)} :
    LocalRewritePattern.PreservesSemantics (binopZeroLeftLocal matchAshr) h h₂ h₃ h₄ :=
  binopZeroLeftLocal_preservesSemantics (srcOp := .ashr)
    (shiftFn := fun x y props => Data.LLVM.Int.ashr x y props.exact)
    (fun hm => ⟨(matchAshr_implies hm).1, (matchAshr_implies hm).2.1, (matchAshr_implies hm).2.2.1⟩)
    (fun opVerif hType => isVerifiedLLVMShift_of_isVerifiedIntegerBinop
      (OperationPtr.Verified.llvm_ashr opVerif hType))
    ashr_zeroLeftSem
    (fun _y props => Data.LLVM.Int.ashr_zero_left (exact := props.exact))

theorem mul_left_to_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (binopZeroLeftLocal matchMul)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (binopZeroLeftLocal matchMul)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (binopZeroLeftLocal matchMul)}
    {h₄ : LocalRewritePattern.ReturnValues (binopZeroLeftLocal matchMul)} :
    LocalRewritePattern.PreservesSemantics (binopZeroLeftLocal matchMul) h h₂ h₃ h₄ :=
  binopZeroLeftLocal_preservesSemantics (srcOp := .mul)
    (shiftFn := fun x y props => Data.LLVM.Int.mul x y props.nsw props.nuw)
    (fun hm => ⟨(matchMul_implies hm).1, (matchMul_implies hm).2.1, (matchMul_implies hm).2.2.1⟩)
    (fun opVerif hType => isVerifiedLLVMShift_of_isVerifiedIntegerBinop
      (OperationPtr.Verified.llvm_mul opVerif hType))
    mul_zeroLeftSem
    (fun _y props => Data.LLVM.Int.mul_zero_left (nsw := props.nsw) (nuw := props.nuw))

/-! ### narrow_binop (`narrow_binop_{add,sub,mul}`)

  `trunc (binop X C) → binop (trunc X) (trunc C)` for `binop ∈ {add, sub, mul}`, at `i64 → i32`,
  when the binop's second operand `C` is a matched integer constant. `op` is the outer `trunc`; its
  operand is a defining `binop X C` (recovered via `matchBinop_getVar?_of_EquationLemmaAt`). Create
  `tx = trunc X`, `tc = trunc C` (`i32`), then `binop tx tc` (`i32`). All three created ops clear
  their overflow flags. The `matchConstantIntVal C` guard is only a firing heuristic — the rewrite is
  bit-for-bit correct regardless of whether `C` is constant — so the proof merely peels it and reads
  the binop's second operand generically.
-/

/-- `llvm.mul` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_mul {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .mul) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `narrow_binop_add`/`narrow_binop_sub`/`narrow_binop_mul`.
    Parameterized over the binop opcode `srcOp`/function `srcFn` (matcher-verifier-purity facts), the
    emitted binop `dst`/`dfn` (`hSemDst`/`hMono`, flags cleared) and the data-refinement lemma
    `hRefine` (`trunc (srcFn X C) ⊒ dfn (trunc X) (trunc C)`). -/
theorem narrowBinopLocal_preservesSemantics {srcOp dst : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {dprops : propertiesOf (.llvm dst)}
    {dfn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    (hSemDst : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (rt : Array TypeAttr) (bo : Array BlockPtr)
        (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (dfn a b)], mem, none)))
    (hMono : ∀ {bw : Nat} (a₁ a₂ b₁ b₂ : Data.LLVM.Int bw), a₁ ⊒ a₂ → b₁ ⊒ b₂ →
        dfn a₁ b₁ ⊒ dfn a₂ b₂)
    (hRefine : ∀ (tnsw tnuw : Bool) (x c : Data.LLVM.Int 64) (po : propertiesOf (.llvm srcOp))
        (hgt : (32 : Nat) < 64),
        Data.LLVM.Int.trunc (srcFn x c po) 32 tnsw tnuw hgt
          ⊒ dfn (Data.LLVM.Int.trunc x 32 false false hgt) (Data.LLVM.Int.trunc c 32 false false hgt))
    {h : LocalRewritePattern.ReturnOps (narrowBinopLocal match? dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (narrowBinopLocal match? dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (narrowBinopLocal match? dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (narrowBinopLocal match? dst dprops)} :
    LocalRewritePattern.PreservesSemantics (narrowBinopLocal match? dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, narrowBinopLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchTrunc` (`op` is the trunc).
  have hMatchSome : (matchTrunc op ctx.raw).isSome := by
    cases hM : matchTrunc op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, tp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchTrunc_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the defining `binop`.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dBin, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hBinSome : (match? dBin ctx.raw).isSome := by
    cases hM : match? dBin ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cst⟩, hBinMatch⟩ := Option.isSome_iff_exists.mp hBinSome
  rw [hBinMatch] at hpattern
  simp only [] at hpattern
  -- Peel the `matchConstantIntVal` guard (its value is not needed).
  have hCstSome : (matchConstantIntVal cst ctx.raw).isSome := by
    cases hM : matchConstantIntVal cst ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cstAttr, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  -- `v0`'s type is an integer type.
  obtain ⟨vty, hvTypeVal⟩ :
      ∃ t, (v0.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (v0.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hvTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hVW
  -- `op`'s result type is an integer type.
  obtain ⟨rty, hrTypeVal⟩ :
      ∃ t, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hrTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  -- Collapse the widths to literals `64`/`32`.
  obtain ⟨vw⟩ := vty; simp only at hVW; subst hVW
  obtain ⟨rw'⟩ := rty; simp only at hRW; subst hRW
  have hw : (32 : Nat) < 64 := by omega
  -- The trunc's single result type, as read by the interpreter.
  have hResTypes0 : op.getResultTypes! ctx.raw = #[((op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  have hResTypes : op.getResultTypes! ctx.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hrTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr)] := by
    rw [hResTypes0]; exact congrArg (fun t => #[t]) (Subtype.ext hrTypeVal)
  -- Unfold the matched `trunc`'s interpretation.
  obtain ⟨v0v, hv0Val, hMem, hRes, hCf⟩ :=
    matchTruncOp_interpretOp_unfold (opType := ⟨64⟩) (resType := ⟨32⟩)
      opInBounds hOpType hNumResults hOperands hProps hResTypes hw
      (by intro w₁ resTy hw' xx pp hIsTy bo mem
          simp [Llvm.interpretOp', ge_iff_le, Nat.not_le.mpr hw', pure, Interp])
      hinterp hvTypeVal
  subst hCf
  -- Recover the defining `binop`'s value and both operands' facts.
  obtain ⟨xv, cv, hxVal, hcVal, hv0BinIs, hxType, hcType, hDomX, hDomC, hxIn, hcIn,
      xNotOp, cNotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := srcOp) (srcFn := srcFn)
      hMatchImplies hVerified hPure hSemSrc ctxDom ctxVerif opInBounds stateWf hDef hBinMatch
      (by rw [hOperands]; simp) hvTypeVal
  -- Pin `v0v` to `srcFn xv cv props`.
  obtain rfl : v0v = srcFn xv cv (dBin.getProperties! ctx.raw (.llvm srcOp)) := by
    have := hv0Val.symm.trans hv0BinIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Type attrs for `x`/`cst` (`i64`) and the result (`i32`).
  have hXTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hCTypeAttr : cst.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hcType ▸ (cst.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hcType
  have hOpResTypeVal : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, hrTypeVal ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hrTypeVal
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hRes
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  -- Peel the three creations (`trunc x`, `trunc cst`, `binop`).
  peelOpCreation!₂ hpattern ctx₁ txOp hTx hDomX hDomX₁ hDomC hDomC₁
  peelOpCreation!₂ hpattern ctx₂ tcOp hTc hDomX₁ hDomX₂ hDomC₁ hDomC₂
  peelOpCreation!₂ hpattern ctx₃ binNewOp hBinNew hDomX₂ hDomX₃ hDomC₂ hDomC₃
  cleanupHpattern hpattern
  have hTxNeTc : txOp ≠ tcOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hTxNeBin : txOp ≠ binNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hTcNeBin : tcOp ≠ binNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- Structural facts: `trunc x`.
  have hTxType : txOp.getOpType! ctx₃.raw = .llvm .trunc := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTx (operation := txOp),
      OperationPtr.getOpType!_WfRewriter_createOp hTc (operation := txOp),
      OperationPtr.getOpType!_WfRewriter_createOp hBinNew (operation := txOp)]
  have hTxOperands : txOp.getOperands! ctx₃.raw = #[x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTx (operation := txOp),
      OperationPtr.getOperands!_WfRewriter_createOp hTc (operation := txOp),
      OperationPtr.getOperands!_WfRewriter_createOp hBinNew (operation := txOp)]
  have hTxProps : txOp.getProperties! ctx₃.raw (.llvm .trunc) = NswNuwProperties.mk false false := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hTx (operation := txOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hTc hTxNeTc,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hBinNew hTxNeBin]
  have hTxResTypes : txOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hTx (operation := txOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hTc (operation := txOp)
    rw [if_neg hTxNeTc] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hBinNew (operation := txOp)
    rw [if_neg hTxNeBin] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hOpResTypeVal
  -- Structural facts: `trunc cst`.
  have hTcType : tcOp.getOpType! ctx₃.raw = .llvm .trunc := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTc (operation := tcOp),
      OperationPtr.getOpType!_WfRewriter_createOp hBinNew (operation := tcOp)]
  have hTcOperands : tcOp.getOperands! ctx₃.raw = #[cst] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTc (operation := tcOp),
      OperationPtr.getOperands!_WfRewriter_createOp hBinNew (operation := tcOp)]
  have hTcProps : tcOp.getProperties! ctx₃.raw (.llvm .trunc) = NswNuwProperties.mk false false := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hTc (operation := tcOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hBinNew hTcNeBin]
  have hTcResTypes : tcOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hTc (operation := tcOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hBinNew (operation := tcOp)
    rw [if_neg hTcNeBin] at hT3
    rw [hT3, hT]
    exact congrArg (fun t => #[t]) hOpResTypeVal
  -- Structural facts: the narrowed `binop`.
  have hBinNewType : binNewOp.getOpType! ctx₃.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hBinNew (operation := binNewOp)]
  have hBinNewOperands : binNewOp.getOperands! ctx₃.raw
      = #[ValuePtr.opResult (txOp.getResult 0), ValuePtr.opResult (tcOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hBinNew (operation := binNewOp)]
  have hBinNewProps : binNewOp.getProperties! ctx₃.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hBinNew (operation := binNewOp)]
  have hBinNewResTypes : binNewOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hBinNew (operation := binNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResTypeVal
  -- Read refined `x`/`cst` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₃ xNotOp
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hcIn hcVal
      hDomC hDomC₃ cNotOp
  -- Replay `trunc x`, then `trunc cst`, then the `binop`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_unaryInt_forward (state := state')
      (inBounds := WfRewriter.createOp_inBounds_mono (ptr := .operation txOp) hBinNew
        (WfRewriter.createOp_inBounds_mono (ptr := .operation txOp) hTc
          (WfRewriter.createOp_new_inBounds txOp hTx)))
      (srcType := ⟨64⟩) (resType := ⟨32⟩)
      (f := fun c => Data.LLVM.Int.trunc c 32 false false (by omega))
      (by intro blockOperands mem
          exact trunc_interpretOp' 64 ⟨32⟩ (by omega) _ (NswNuwProperties.mk false false) _
            blockOperands mem)
      hTxType hTxProps hTxOperands hTxResTypes hXVal'
  have hCVal₁ : s₁.variables.getVar? cst = some (RuntimeValue.int 64 ct) := by
    rw [hFrame₁ cst (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hcIn
      (WfRewriter.createOp_new_not_inBounds txOp hTx))]
    exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁)
      (inBounds := WfRewriter.createOp_inBounds_mono (ptr := .operation tcOp) hBinNew
        (WfRewriter.createOp_new_inBounds tcOp hTc))
      (srcType := ⟨64⟩) (resType := ⟨32⟩)
      (f := fun c => Data.LLVM.Int.trunc c 32 false false (by omega))
      (by intro blockOperands mem
          exact trunc_interpretOp' 64 ⟨32⟩ (by omega) _ (NswNuwProperties.mk false false) _
            blockOperands mem)
      hTcType hTcProps hTcOperands hTcResTypes hCVal₁
  have hTxResIn₁ : (ValuePtr.opResult (txOp.getResult 0)).InBounds ctx₁.raw := by
    have hnr : txOp.getNumResults! ctx₁.raw = 1 := by
      grind [OperationPtr.getNumResults!_WfRewriter_createOp hTx (operation := txOp)]
    clear valueRefinement state'Dom state'Wf hpattern
    rw [ValuePtr.inBounds_opResult]
    refine ⟨WfRewriter.createOp_new_inBounds txOp hTx, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hTxRes₂ : s₂.variables.getVar? (ValuePtr.opResult (txOp.getResult 0))
      = some (RuntimeValue.int 32 (Data.LLVM.Int.trunc xt 32 false false (by omega))) := by
    rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hTxResIn₁
      (WfRewriter.createOp_new_not_inBounds tcOp hTc))]
    exact hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₂)
      (inBounds := WfRewriter.createOp_new_inBounds binNewOp hBinNew)
      (it := ⟨32⟩) (f := fun a b => dfn a b)
      (by intro resultTypes blockOperands mem; exact hSemDst _ _ _ _ _ _)
      hBinNewType hBinNewProps hBinNewOperands hBinNewResTypes hTxRes₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 32 (dfn (Data.LLVM.Int.trunc xt 32 false false (by omega))
      (Data.LLVM.Int.trunc ct 32 false false (by omega)))],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `trunc (srcFn xv cv) ⊒ dfn (trunc xv) (trunc cv) ⊒ dfn (trunc xt) (trunc ct)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine tp.nsw tp.nuw xv cv _ hw)
    (hMono _ _ _ _ (Data.LLVM.Int.trunc_mono xv xt (by omega) hxRef)
      (Data.LLVM.Int.trunc_mono cv ct (by omega) hcRef))

theorem narrow_binop_add_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (narrowBinopLocal (matchBinopNoProps matchAdd) .add (NswNuwProperties.mk false false))
      h h₂ h₃ h₄ :=
  narrowBinopLocal_preservesSemantics (srcOp := .add) (dst := .add)
    (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
    (dfn := fun a b => Data.LLVM.Int.add a b)
    (matchBinopNoProps_implies matchAdd_implies) OperationPtr.Verified.llvm_add
    (fun h => OperationPtr.Pure.llvm_add h)
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.add_mono a₁ b₁ a₂ b₂ h₁ h₂ false false)
    (fun tnsw tnuw x c po _ => by
      simpa using Data.LLVM.Int.NarrowBinopAdd (s := tnsw) (u := tnuw) (nsw := po.nsw) (nuw := po.nuw))

theorem narrow_binop_sub_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (narrowBinopLocal (matchBinopNoProps matchSub) .sub (NswNuwProperties.mk false false))
      h h₂ h₃ h₄ :=
  narrowBinopLocal_preservesSemantics (srcOp := .sub) (dst := .sub)
    (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
    (dfn := fun a b => Data.LLVM.Int.sub a b)
    (matchBinopNoProps_implies matchSub_implies) OperationPtr.Verified.llvm_sub
    (fun h => OperationPtr.Pure.llvm_sub h)
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.sub_mono a₁ b₁ a₂ b₂ h₁ h₂ false false)
    (fun tnsw tnuw x c po _ => by
      simpa using Data.LLVM.Int.NarrowBinopSub (s := tnsw) (u := tnuw) (nsw := po.nsw) (nuw := po.nuw))

theorem narrow_binop_mul_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (narrowBinopLocal (matchBinopNoProps matchMul) .mul (NswNuwProperties.mk false false))
      h h₂ h₃ h₄ :=
  narrowBinopLocal_preservesSemantics (srcOp := .mul) (dst := .mul)
    (srcFn := fun a b p => Data.LLVM.Int.mul a b p.nsw p.nuw)
    (dfn := fun a b => Data.LLVM.Int.mul a b)
    (matchBinopNoProps_implies matchMul_implies) OperationPtr.Verified.llvm_mul
    (fun h => OperationPtr.Pure.llvm_mul h)
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Data.LLVM.Int.mul_mono a₁ b₁ a₂ b₂ h₁ h₂ false false)
    (fun tnsw tnuw x c po _ => by
      simpa using Data.LLVM.Int.NarrowBinopMul (s := tnsw) (u := tnuw) (nsw := po.nsw) (nuw := po.nuw))

/-! ### cast-chain combines (`truncate_of_sext`, `{zext,sext}_of_{zext,sext}`)

  `trunc (sext x) → x` (round-trip; mirror of `trunc_of_zext`), and `cast (cast x) → cast x`
  for `cast ∈ {zext, sext}` (the shared `castOfCastLocal` combinator). All match an outer cast
  whose operand is a defining cast of the same kind, recovered via the `*_getVar?_of_EquationLemmaAt`
  graph lemmas, and reach the `veir_bv_decide` data lemmas in `LLVMProofs.lean`.
-/

set_option maxHeartbeats 1000000 in
/-- `trunc (sext x) → x` when the `trunc` lands back on `x`'s type. The mirror of
    `trunc_of_zext_local_preservesSemantics`, with the defining `sext` recovered via
    `sext_getVar?_of_EquationLemmaAt` and the data lemma `Data.LLVM.Int.trunc_of_sext`. -/
theorem truncate_of_sext_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps truncate_of_sext_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges truncate_of_sext_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds truncate_of_sext_local}
    {h₄ : LocalRewritePattern.ReturnValues truncate_of_sext_local} :
    LocalRewritePattern.PreservesSemantics truncate_of_sext_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, truncate_of_sext_local]
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
  -- Peel the defining `sext`.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨sextOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSextSome : (matchSext sextOp ctx.raw).isSome := by
    cases hM : matchSext sextOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, sProps⟩, hSext⟩ := Option.isSome_iff_exists.mp hSextSome
  rw [hSext] at hpattern
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
  -- Recover the defining `sext`'s value.
  obtain ⟨opType', hw', xv, hxVal, hv0SextVal, hxType', hDomX, hxIn, hxNotRes⟩ :=
    sext_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hSext
      (by rw [hOperands]; simp) hzTypeVal
  obtain rfl : opType' = ⟨32⟩ := by rw [hxType'] at hxTypeVal; grind
  obtain rfl : v0v = Data.LLVM.Int.sext xv 64 hw' := by
    have := hv0Val.symm.trans hv0SextVal; simpa using this
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
  -- `trunc (sext x) ⊒ x` at the guarded widths, then transport along `x ⊒ xt`.
  have hLem := Data.LLVM.Int.trunc_of_sext (s := tProps.nsw) (u := tProps.nuw) (x := xv)
  exact isRefinedBy_trans (by simpa using hLem) hxRef

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `zext_of_zext`/`sext_of_sext`, both instances of
    `castOfCastLocal`. `op` is the outer cast; its operand is a defining cast of the same kind
    (recovered via the `*_getVar?_of_EquationLemmaAt` graph lemma passed as `hGraph`). Create a
    single `cast` straight from the innermost value `x`. Parameterized over the cast opcode, its
    matcher, the created op's properties `cprops`, the data function `srcFn` (`hSemSrc`), the graph
    lemma (`hGraph`), its monotonicity (`hMono`), and the value-refinement lemma (`hRefine`). -/
theorem castOfCastLocal_preservesSemantics {cast : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × propertiesOf (.llvm cast))}
    {cprops : propertiesOf (.llvm cast)}
    {srcFn : ∀ {w₁ w₂ : Nat}, Data.LLVM.Int w₁ → w₁ < w₂ → propertiesOf (.llvm cast) →
      Data.LLVM.Int w₂}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {operand props},
        match? opp c = some (operand, props) →
        opp.getOpType! c = .llvm cast ∧ opp.getNumResults! c = 1 ∧
        opp.getOperands! c = #[operand] ∧ props = opp.getProperties! c (.llvm cast))
    (hSemSrc : ∀ (w₁ : Nat) (retTy : IntegerType) (hw : w₁ < retTy.bitwidth)
        (x : Data.LLVM.Int w₁) (props : propertiesOf (.llvm cast)) (hIsTy)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' cast props #[⟨.integerType retTy, hIsTy⟩] #[.int w₁ x] blockOperands mem
          = some (.ok (#[.int retTy.bitwidth (srcFn x hw props)], mem, none)))
    (hGraph : ∀ {c : WfIRContext OpCode} (_cDom : c.Dom) (_cVerif : c.Verified)
        {opp : OperationPtr} (oib : opp.InBounds c.raw)
        {st : InterpreterState c}
        (_stWf : st.EquationLemmaAt (InsertPoint.before opp) (by grind))
        {base x : ValuePtr} {castOp : OperationPtr} {cP : propertiesOf (.llvm cast)}
        {retType : IntegerType}
        (_hDef : getDefiningOp base c.raw = some castOp)
        (_hMatch : match? castOp c.raw = some (x, cP))
        (_hOperand : base ∈ opp.getOperands! c.raw)
        (_hBaseType : (base.getType! c.raw).val = Attribute.integerType retType),
        ∃ (opType : IntegerType) (hw : opType.bitwidth < retType.bitwidth)
          (xv : Data.LLVM.Int opType.bitwidth),
          st.variables.getVar? x = some (RuntimeValue.int opType.bitwidth xv) ∧
          st.variables.getVar? base = some (RuntimeValue.int retType.bitwidth (srcFn xv hw cP)) ∧
          (x.getType! c.raw).val = Attribute.integerType opType ∧
          x.dominatesIp (InsertPoint.before opp) c ∧
          x.InBounds c.raw ∧
          x ∉ opp.getResults! c.raw)
    (hMono : ∀ {w₁ w₂ : Nat} (x₁ x₂ : Data.LLVM.Int w₁) (hw : w₁ < w₂)
        (p : propertiesOf (.llvm cast)), x₁ ⊒ x₂ → srcFn x₁ hw p ⊒ srcFn x₂ hw p)
    (hRefine : ∀ (p0 p1 : propertiesOf (.llvm cast)) (xv : Data.LLVM.Int 8)
        (hwX : (8 : Nat) < 32) (hwO : (32 : Nat) < 64) (hwC : (8 : Nat) < 64),
        srcFn (srcFn xv hwX p0) hwO p1 ⊒ srcFn xv hwC cprops)
    {h : LocalRewritePattern.ReturnOps (castOfCastLocal cast match? cprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (castOfCastLocal cast match? cprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (castOfCastLocal cast match? cprops)}
    {h₄ : LocalRewritePattern.ReturnValues (castOfCastLocal cast match? cprops)} :
    LocalRewritePattern.PreservesSemantics (castOfCastLocal cast match? cprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, castOfCastLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer cast.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, outerProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := hMatchImplies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the defining cast.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dC, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hInnerSome : (match? dC ctx.raw).isSome := by
    cases hM : match? dC ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, innerProps⟩, hInner⟩ := Option.isSome_iff_exists.mp hInnerSome
  rw [hInner] at hpattern
  simp only [] at hpattern
  -- Peel the three type reads.
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
  obtain ⟨rty, hrTypeVal⟩ :
      ∃ t, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hrTypeVal] at hpattern
  simp only [] at hpattern
  -- Width guard: `x : i8`, `v0 : i32`, result `: i64`.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  obtain ⟨bwx⟩ := xt
  obtain ⟨bwz⟩ := zt
  obtain ⟨bwr⟩ := rty
  simp only at hWidthRaw hxTypeVal hzTypeVal hrTypeVal
  obtain ⟨rfl, rfl, rfl⟩ : bwx = 8 ∧ bwz = 32 ∧ bwr = 64 := by omega
  -- The op's single result type (`i64`), as read by the interpreter.
  have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨64⟩ := hrTypeVal
  have hResTypes0 : op.getResultTypes! ctx.raw = #[((op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
      obtain rfl : i = 0 := by omega
      have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw) (index := 0)
        (by omega)
      grind
  have hResTypes : op.getResultTypes! ctx.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr)] := by
    rw [hResTypes0]; exact congrArg (fun t => #[t]) (Subtype.ext hResType)
  have hw3264 : (IntegerType.mk 32).bitwidth < (IntegerType.mk 64).bitwidth := by decide
  have hwC : (8 : Nat) < 64 := by omega
  -- Unfold the outer cast's interpretation.
  obtain ⟨v0v, hv0Val, hMem, hResSrc, hCf⟩ :=
    matchExtOp_interpretOp_unfold (srcOp := cast) (srcFn := srcFn) (props := outerProps)
      opInBounds hOpType hNumResults hOperands hProps hResTypes hw3264 hSemSrc hinterp hzTypeVal
  subst hCf
  -- Recover the defining cast's value.
  obtain ⟨opType', hw', xv, hxVal, hv0CastIs, hxType', hDomX, hxIn, hxNotRes⟩ :=
    hGraph ctxDom ctxVerif opInBounds stateWf hDef hInner (by rw [hOperands]; simp) hzTypeVal
  obtain rfl : opType' = ⟨8⟩ := by rw [hxType'] at hxTypeVal; grind
  obtain rfl : v0v = srcFn xv hw' innerProps := by
    have := hv0Val.symm.trans hv0CastIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hResSrc] at hsourceValues
  subst sourceValues
  -- Peel the single cast creation.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomX hDomX₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm cast := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[x] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.llvm cast) = cprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType ⟨64⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩
          : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) (Subtype.ext hResType)
  -- Read the refined innermost value `x` in the target state.
  obtain ⟨xtv, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₁ hxNotRes
  -- Replay the created cast forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_unaryInt_forward (state := state') (inBounds := by grind)
      (srcType := ⟨8⟩) (resType := ⟨64⟩) (f := fun c => srcFn c hwC cprops)
      (by intro blockOperands mem; exact hSemSrc 8 ⟨64⟩ hwC xtv cprops _ blockOperands mem)
      hNewType hNewProps hNewOperands hNewResTypes hXVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64 (srcFn xtv hwC cprops)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `srcFn (srcFn xv ..) .. ⊒ srcFn xv .. cprops ⊒ srcFn xtv .. cprops`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine innerProps outerProps xv hw' hw3264 hwC)
    (hMono xv xtv hwC cprops hxRef)

theorem zext_of_zext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics zext_of_zext_local h h₂ h₃ h₄ :=
  castOfCastLocal_preservesSemantics (cast := .zext) (match? := matchZext)
    (cprops := { nneg := false })
    (srcFn := fun a hw p => Data.LLVM.Int.zext a _ p.nneg hw)
    matchZext_implies zext_interpretOp'
    zext_getVar?_of_EquationLemmaAt
    (fun x₁ x₂ hw p hr => Data.LLVM.Int.zext_mono x₁ x₂ hw hr)
    (fun p0 p1 xv _ _ _ => by
       simpa using Data.LLVM.Int.zext_of_zext (n0 := p0.nneg) (n1 := p1.nneg) (x := xv))

theorem sext_of_sext_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics sext_of_sext_local h h₂ h₃ h₄ :=
  castOfCastLocal_preservesSemantics (cast := .sext) (match? := matchSext) (cprops := ())
    (srcFn := fun a hw _ => Data.LLVM.Int.sext a _ hw)
    matchSext_implies sext_interpretOp'
    sext_getVar?_of_EquationLemmaAt
    (fun x₁ x₂ hw _ hr => Data.LLVM.Int.sext_mono x₁ x₂ hw hr)
    (fun _ _ xv _ _ _ => by simpa using Data.LLVM.Int.sext_of_sext (x := xv))

/-! ### Constant reassociation combines

  `(A ± C1) ± C2 → A ± fold(C1, C2)` and the `C2 - (A + C1)` / `(C1 - A) - C2` variants. Each combine
  matches an outer binop whose one operand is a constant `C2` and whose other operand is a defining
  binop with its own constant operand `C1`; it creates a fresh `llvm.mlir.constant` holding the
  folded value and one arithmetic op (whose overflow flags are *cleared* — see the flag-threading
  note in `LLVMProofs.lean`). The proofs follow `NotAPlusNegOne_local_preservesSemantics`: unfold the
  outer op's interpretation, pin its constant operand with `matchConstantIntVal_getVar?…`, recover
  the defining binop's value (with its constant operand pinned) with a `matchBinop*Const_getVar?…`
  graph lemma, then replay the created constant (`interpretOp_llvm_constant_forward`) and op
  (`interpretOp_llvm_binaryInt_forward`) and close with the matching `Data.LLVM.Int.*` data lemma. -/

/-- Variant of `matchBinopSndConst_getVar?_of_EquationLemmaAt` for a defining `binop (const c) X`:
    the *first* operand is the matched integer constant `c`. Returns the second operand `X`'s facts,
    with `base`'s value pinned to `srcFn (constant c) xv props`. Needed by `C1MinusAMinusC2`, whose
    inner `sub C1 A` has the constant first. -/
private theorem matchBinopFstConst_getVar?_of_EquationLemmaAt {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base c x : ValuePtr} {binOp : OperationPtr} {cAttr : IntegerAttr} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some binOp)
    (hMatch : match? binOp ctx.raw = some (c, x))
    (hCst : matchConstantIntVal c ctx.raw = some cAttr)
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (srcFn (Data.LLVM.Int.constant intType.bitwidth cAttr.value) xv
          (binOp.getProperties! ctx.raw (.llvm srcOp)))) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  -- The binop's value and both operands' facts (generic lemma). Here operand 0 is the constant `c`
  -- and operand 1 is `x`.
  obtain ⟨cv, xv, hcVal, hxVal, hBaseVal, hcType, hxType, hDomC, hDomX, hcIn, hxIn,
      cNotOp, xNotOp⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt hMatchImplies hVerified hPure hSemSrc ctxDom ctxVerif
      opInBounds stateWf hDef hMatch hOperand hBaseType
  -- Pin the constant operand `c` to `constant cAttr.value`.
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hCst
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    rw [← heq]; exact Subtype.ext hcType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  -- `binOp` strictly dominates `op` (it defines `base`, an operand of `op`).
  obtain ⟨hBinType, hBinNumResults, hBinOperands⟩ := hMatchImplies hMatch
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hBinOpEq : basePtr.op = binOp := by simp [getDefiningOp] at hDef; grind
  subst hBinOpEq
  have hBinOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hBaseInb : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hBaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!, OpResultPtr.InBounds]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hBinDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hBinOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hBinSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hBinDefines hOperand
  -- `cstPtr.op` strictly dominates `binOp` (it defines the constant operand), hence `op`.
  have hCstSDomBin : cstPtr.op.strictlyDominates basePtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCstDefines (by rw [hBinOperands]; simp)
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomBin hBinSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType
      hInterpCst
  obtain rfl : cv = Data.LLVM.Int.constant intType.bitwidth cAttr.value := by
    rw [hCstEq] at hcVal; grind
  exact ⟨xv, hxVal, hBaseVal, hxType, hDomX, hxIn, xNotOp⟩

set_option maxHeartbeats 1000000 in
theorem APlusC1MinusC2_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps APlusC1MinusC2_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges APlusC1MinusC2_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds APlusC1MinusC2_local}
    {h₄ : LocalRewritePattern.ReturnValues APlusC1MinusC2_local} :
    LocalRewritePattern.PreservesSemantics APlusC1MinusC2_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, APlusC1MinusC2_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[addVal, c2v]`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨addVal, c2v, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the outer constant `c2v`.
  have hC2Some : (matchConstantIntVal c2v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c2v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c2Attr, hC2⟩ := Option.isSome_iff_exists.mp hC2Some
  rw [hC2] at hpattern
  simp only [] at hpattern
  -- Peel the defining `add` of `addVal`, and its constant operand `c1v`.
  have hDefSome : (getDefiningOp addVal ctx.raw).isSome := by
    cases hM : getDefiningOp addVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, c1v, aProps⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1] at hpattern
  simp only [] at hpattern
  -- Verifier facts for the outer `sub`: operands/result share type `subType`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hAddValEq : addVal = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hC2vEq : c2v = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = addVal := by
    rw [hAddValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = c2v := by
    rw [hC2vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAddValType : (addVal.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hC2vType : (c2v.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  -- Unfold the outer `sub`'s interpretation.
  obtain ⟨addValVal, c2vVal, hAddValVal, hC2vVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hAddValType hC2vType
  subst hCf
  -- Recover the defining `add a (const c1)`'s value (with `c1` pinned), and `a`'s facts.
  obtain ⟨av, haVal, hAddValIs, haType, hDomA, haIn, aNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .add)
      (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchAdd_implies)
      OperationPtr.Verified.llvm_add OperationPtr.Pure.llvm_add
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchAdd addOp ctx.raw = some (a, c1v) by
        simp only [matchBinopNoProps, bind, Option.bind, hAdd])
      hC1 (by rw [hSubOperands]; simp) hAddValType
  have hApEq : addOp.getProperties! ctx.raw (.llvm .add) = aProps := ((matchAdd_implies hAdd).2.2.2).symm
  rw [hApEq] at hAddValIs
  -- Pin `addValVal` and the outer constant `c2vVal`.
  obtain rfl : addValVal
      = Data.LLVM.Int.add av (Data.LLVM.Int.constant subType.bitwidth c1Attr.value)
          aProps.nsw aProps.nuw := by
    have := hAddValVal.symm.trans hAddValIs; simpa using this
  have hC2vConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC2 (by rw [hSubOperands]; simp) hC2vType
  obtain rfl : c2vVal = Data.LLVM.Int.constant subType.bitwidth c2Attr.value := by
    have := hC2vVal.symm.trans hC2vConst; simpa using this
  -- Width guard on `a`'s type.
  rw [haType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : subType.bitwidth = 64 ∨ subType.bitwidth = 32 := by omega
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the two creations: the folded constant, then the `add`.
  peelOpCreation! hpattern ctx₁ cfOp hCf hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ addNewOp hAddNew hDomA₁ hDomA₂
  cleanupHpattern hpattern
  have hCfNeAdd : cfOp ≠ addNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `a`'s type as a `TypeAttr`, transported to `ctx₁`.
  have haTypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have haTypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCf haIn]; exact haTypeAttr
  -- Structural facts for the folded constant.
  have hCfType : cfOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := cfOp)]
  have hCfOperands : cfOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := cfOp)]
  have hCfProps : (cfOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨c1Attr.value - c2Attr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCf (operation := cfOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hCfNeAdd, h1]
  have hCfResTypes : cfOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCf (operation := cfOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := cfOp)
    rw [if_neg hCfNeAdd] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) haTypeAttr
  -- Structural facts for the new `add`.
  have hAddNewType : addNewOp.getOpType! ctx₂.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewOperands : addNewOp.getOperands! ctx₂.raw = #[a, ValuePtr.opResult (cfOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewProps : addNewOp.getProperties! ctx₂.raw (.llvm .add) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewResTypes : addNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := addNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) haTypeAttr₁
  -- Read the refined `a` in the target state.
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      hDomA hDomA₂ aNotOp
  -- Replay the folded constant, then the `add`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCfType hCfProps hCfOperands hCfResTypes
  have haVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int subType.bitwidth at') := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cfOp hCf))]
    exact haVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.add x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddNewType hAddNewProps hAddNewOperands hAddNewResTypes haVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.add at' (Data.LLVM.Int.constant subType.bitwidth
        (c1Attr.value - c2Attr.value)) false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble.
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.APlusC1MinusC2 hWidth)
    (Data.LLVM.Int.add_mono _ _ _ _ haRef (isRefinedBy_refl _) false false)

set_option maxHeartbeats 1000000 in
theorem C2MinusAPlusC1_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps C2MinusAPlusC1_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges C2MinusAPlusC1_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds C2MinusAPlusC1_local}
    {h₄ : LocalRewritePattern.ReturnValues C2MinusAPlusC1_local} :
    LocalRewritePattern.PreservesSemantics C2MinusAPlusC1_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, C2MinusAPlusC1_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[c2v, addVal]` (constant *first*).
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨c2v, addVal, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have hC2Some : (matchConstantIntVal c2v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c2v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c2Attr, hC2⟩ := Option.isSome_iff_exists.mp hC2Some
  rw [hC2] at hpattern
  simp only [] at hpattern
  have hDefSome : (getDefiningOp addVal ctx.raw).isSome := by
    cases hM : getDefiningOp addVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨addOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hAddSome : (matchAdd addOp ctx.raw).isSome := by
    cases hM : matchAdd addOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, c1v, aProps⟩, hAdd⟩ := Option.isSome_iff_exists.mp hAddSome
  rw [hAdd] at hpattern
  simp only [] at hpattern
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hC2vEq : c2v = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hAddValEq : addVal = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = c2v := by
    rw [hC2vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = addVal := by
    rw [hAddValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hC2vType : (c2v.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hAddValType : (addVal.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  obtain ⟨c2vVal, addValVal, hC2vVal, hAddValVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hC2vType hAddValType
  subst hCf
  obtain ⟨av, haVal, hAddValIs, haType, hDomA, haIn, aNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .add)
      (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchAdd_implies)
      OperationPtr.Verified.llvm_add OperationPtr.Pure.llvm_add
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchAdd addOp ctx.raw = some (a, c1v) by
        simp only [matchBinopNoProps, bind, Option.bind, hAdd])
      hC1 (by rw [hSubOperands]; simp) hAddValType
  have hApEq : addOp.getProperties! ctx.raw (.llvm .add) = aProps := ((matchAdd_implies hAdd).2.2.2).symm
  rw [hApEq] at hAddValIs
  obtain rfl : addValVal
      = Data.LLVM.Int.add av (Data.LLVM.Int.constant subType.bitwidth c1Attr.value)
          aProps.nsw aProps.nuw := by
    have := hAddValVal.symm.trans hAddValIs; simpa using this
  have hC2vConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC2 (by rw [hSubOperands]; simp) hC2vType
  obtain rfl : c2vVal = Data.LLVM.Int.constant subType.bitwidth c2Attr.value := by
    have := hC2vVal.symm.trans hC2vConst; simpa using this
  rw [haType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : subType.bitwidth = 64 ∨ subType.bitwidth = 32 := by omega
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  peelOpCreation! hpattern ctx₁ cfOp hCf hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ subNewOp hSubNew hDomA₁ hDomA₂
  cleanupHpattern hpattern
  have hCfNeSub : cfOp ≠ subNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have haTypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have haTypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCf haIn]; exact haTypeAttr
  have hCfType : cfOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfOperands : cfOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfProps : (cfOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨c2Attr.value - c1Attr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCf (operation := cfOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSubNew hCfNeSub, h1]
  have hCfResTypes : cfOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCf (operation := cfOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := cfOp)
    rw [if_neg hCfNeSub] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) haTypeAttr
  have hSubNewType : subNewOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewOperands : subNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (cfOp.getResult 0), a] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewProps : subNewOp.getProperties! ctx₂.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewResTypes : subNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := subNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) haTypeAttr₁
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      hDomA hDomA₂ aNotOp
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCfType hCfProps hCfOperands hCfResTypes
  have haVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int subType.bitwidth at') := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cfOp hCf))]
    exact haVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.sub x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubNewType hSubNewProps hSubNewOperands hSubNewResTypes hRes₁ haVal₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.sub (Data.LLVM.Int.constant subType.bitwidth
        (c2Attr.value - c1Attr.value)) at' false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.C2MinusAPlusC1 hWidth)
    (Data.LLVM.Int.sub_mono _ _ _ _ (isRefinedBy_refl _) haRef false false)

set_option maxHeartbeats 1000000 in
theorem AMinusC1MinusC2_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps AMinusC1MinusC2_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges AMinusC1MinusC2_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds AMinusC1MinusC2_local}
    {h₄ : LocalRewritePattern.ReturnValues AMinusC1MinusC2_local} :
    LocalRewritePattern.PreservesSemantics AMinusC1MinusC2_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, AMinusC1MinusC2_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[subVal, c2v]`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨subVal, c2v, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have hC2Some : (matchConstantIntVal c2v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c2v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c2Attr, hC2⟩ := Option.isSome_iff_exists.mp hC2Some
  rw [hC2] at hpattern
  simp only [] at hpattern
  have hDefSome : (getDefiningOp subVal ctx.raw).isSome := by
    cases hM : getDefiningOp subVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨subInnerOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSub2Some : (matchSub subInnerOp ctx.raw).isSome := by
    cases hM : matchSub subInnerOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, c1v, sInnerProps⟩, hSub2⟩ := Option.isSome_iff_exists.mp hSub2Some
  rw [hSub2] at hpattern
  simp only [] at hpattern
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hSubValEq : subVal = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hC2vEq : c2v = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = subVal := by
    rw [hSubValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = c2v := by
    rw [hC2vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hSubValType : (subVal.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hC2vType : (c2v.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  obtain ⟨subValVal, c2vVal, hSubValVal, hC2vVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hSubValType hC2vType
  subst hCf
  obtain ⟨av, haVal, hSubValIs, haType, hDomA, haIn, aNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchSub_implies)
      OperationPtr.Verified.llvm_sub OperationPtr.Pure.llvm_sub
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchSub subInnerOp ctx.raw = some (a, c1v) by
        simp only [matchBinopNoProps, bind, Option.bind, hSub2])
      hC1 (by rw [hSubOperands]; simp) hSubValType
  have hSpEq : subInnerOp.getProperties! ctx.raw (.llvm .sub) = sInnerProps :=
    ((matchSub_implies hSub2).2.2.2).symm
  rw [hSpEq] at hSubValIs
  obtain rfl : subValVal
      = Data.LLVM.Int.sub av (Data.LLVM.Int.constant subType.bitwidth c1Attr.value)
          sInnerProps.nsw sInnerProps.nuw := by
    have := hSubValVal.symm.trans hSubValIs; simpa using this
  have hC2vConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC2 (by rw [hSubOperands]; simp) hC2vType
  obtain rfl : c2vVal = Data.LLVM.Int.constant subType.bitwidth c2Attr.value := by
    have := hC2vVal.symm.trans hC2vConst; simpa using this
  rw [haType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : subType.bitwidth = 64 ∨ subType.bitwidth = 32 := by omega
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  peelOpCreation! hpattern ctx₁ cfOp hCf hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ subNewOp hSubNew hDomA₁ hDomA₂
  cleanupHpattern hpattern
  have hCfNeSub : cfOp ≠ subNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have haTypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have haTypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCf haIn]; exact haTypeAttr
  have hCfType : cfOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfOperands : cfOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfProps : (cfOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨c1Attr.value + c2Attr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCf (operation := cfOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSubNew hCfNeSub, h1]
  have hCfResTypes : cfOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCf (operation := cfOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := cfOp)
    rw [if_neg hCfNeSub] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) haTypeAttr
  have hSubNewType : subNewOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewOperands : subNewOp.getOperands! ctx₂.raw
      = #[a, ValuePtr.opResult (cfOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewProps : subNewOp.getProperties! ctx₂.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewResTypes : subNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := subNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) haTypeAttr₁
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      hDomA hDomA₂ aNotOp
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCfType hCfProps hCfOperands hCfResTypes
  have haVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int subType.bitwidth at') := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cfOp hCf))]
    exact haVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.sub x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubNewType hSubNewProps hSubNewOperands hSubNewResTypes haVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.sub at' (Data.LLVM.Int.constant subType.bitwidth
        (c1Attr.value + c2Attr.value)) false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.AMinusC1MinusC2 hWidth)
    (Data.LLVM.Int.sub_mono _ _ _ _ haRef (isRefinedBy_refl _) false false)

set_option maxHeartbeats 1000000 in
theorem C1MinusAMinusC2_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps C1MinusAMinusC2_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges C1MinusAMinusC2_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds C1MinusAMinusC2_local}
    {h₄ : LocalRewritePattern.ReturnValues C1MinusAMinusC2_local} :
    LocalRewritePattern.PreservesSemantics C1MinusAMinusC2_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, C1MinusAMinusC2_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[subVal, c2v]`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨subVal, c2v, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have hC2Some : (matchConstantIntVal c2v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c2v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c2Attr, hC2⟩ := Option.isSome_iff_exists.mp hC2Some
  rw [hC2] at hpattern
  simp only [] at hpattern
  have hDefSome : (getDefiningOp subVal ctx.raw).isSome := by
    cases hM : getDefiningOp subVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨subInnerOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSub2Some : (matchSub subInnerOp ctx.raw).isSome := by
    cases hM : matchSub subInnerOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨c1v, a, sInnerProps⟩, hSub2⟩ := Option.isSome_iff_exists.mp hSub2Some
  rw [hSub2] at hpattern
  simp only [] at hpattern
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hSubValEq : subVal = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hC2vEq : c2v = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = subVal := by
    rw [hSubValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = c2v := by
    rw [hC2vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hSubValType : (subVal.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hC2vType : (c2v.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  obtain ⟨subValVal, c2vVal, hSubValVal, hC2vVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hSubValType hC2vType
  subst hCf
  -- Inner `sub (const c1) A`: the constant is the *first* operand.
  obtain ⟨av, haVal, hSubValIs, haType, hDomA, haIn, aNotOp⟩ :=
    matchBinopFstConst_getVar?_of_EquationLemmaAt (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchSub_implies)
      OperationPtr.Verified.llvm_sub OperationPtr.Pure.llvm_sub
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchSub subInnerOp ctx.raw = some (c1v, a) by
        simp only [matchBinopNoProps, bind, Option.bind, hSub2])
      hC1 (by rw [hSubOperands]; simp) hSubValType
  have hSpEq : subInnerOp.getProperties! ctx.raw (.llvm .sub) = sInnerProps :=
    ((matchSub_implies hSub2).2.2.2).symm
  rw [hSpEq] at hSubValIs
  obtain rfl : subValVal
      = Data.LLVM.Int.sub (Data.LLVM.Int.constant subType.bitwidth c1Attr.value) av
          sInnerProps.nsw sInnerProps.nuw := by
    have := hSubValVal.symm.trans hSubValIs; simpa using this
  have hC2vConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC2 (by rw [hSubOperands]; simp) hC2vType
  obtain rfl : c2vVal = Data.LLVM.Int.constant subType.bitwidth c2Attr.value := by
    have := hC2vVal.symm.trans hC2vConst; simpa using this
  rw [haType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : subType.bitwidth = 64 ∨ subType.bitwidth = 32 := by omega
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  peelOpCreation! hpattern ctx₁ cfOp hCf hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ subNewOp hSubNew hDomA₁ hDomA₂
  cleanupHpattern hpattern
  have hCfNeSub : cfOp ≠ subNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have haTypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have haTypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCf haIn]; exact haTypeAttr
  have hCfType : cfOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfOperands : cfOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := cfOp)]
  have hCfProps : (cfOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨c1Attr.value - c2Attr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCf (operation := cfOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hSubNew hCfNeSub, h1]
  have hCfResTypes : cfOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCf (operation := cfOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := cfOp)
    rw [if_neg hCfNeSub] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) haTypeAttr
  have hSubNewType : subNewOp.getOpType! ctx₂.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewOperands : subNewOp.getOperands! ctx₂.raw
      = #[ValuePtr.opResult (cfOp.getResult 0), a] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewProps : subNewOp.getProperties! ctx₂.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSubNew (operation := subNewOp)]
  have hSubNewResTypes : subNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSubNew (operation := subNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) haTypeAttr₁
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      hDomA hDomA₂ aNotOp
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCfType hCfProps hCfOperands hCfResTypes
  have haVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int subType.bitwidth at') := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cfOp hCf))]
    exact haVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.sub x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubNewType hSubNewProps hSubNewOperands hSubNewResTypes hRes₁ haVal₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.sub (Data.LLVM.Int.constant subType.bitwidth
        (c1Attr.value - c2Attr.value)) at' false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.C1MinusAMinusC2 hWidth)
    (Data.LLVM.Int.sub_mono _ _ _ _ (isRefinedBy_refl _) haRef false false)

set_option maxHeartbeats 1000000 in
theorem AMinusC1PlusC2_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps AMinusC1PlusC2_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges AMinusC1PlusC2_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds AMinusC1PlusC2_local}
    {h₄ : LocalRewritePattern.ReturnValues AMinusC1PlusC2_local} :
    LocalRewritePattern.PreservesSemantics AMinusC1PlusC2_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, AMinusC1PlusC2_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchAdd op`: operands `#[subVal, c2v]`.
  have hMatchSome : (matchAdd op ctx.raw).isSome := by
    cases hM : matchAdd op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨subVal, c2v, aProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hAddType, hAddNumResults, hAddOperands, -⟩ := matchAdd_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have hC2Some : (matchConstantIntVal c2v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c2v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c2Attr, hC2⟩ := Option.isSome_iff_exists.mp hC2Some
  rw [hC2] at hpattern
  simp only [] at hpattern
  have hDefSome : (getDefiningOp subVal ctx.raw).isSome := by
    cases hM : getDefiningOp subVal ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨subInnerOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSub2Some : (matchSub subInnerOp ctx.raw).isSome := by
    cases hM : matchSub subInnerOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, c1v, sInnerProps⟩, hSub2⟩ := Option.isSome_iff_exists.mp hSub2Some
  rw [hSub2] at hpattern
  simp only [] at hpattern
  have hC1Some : (matchConstantIntVal c1v ctx.raw).isSome := by
    cases hM : matchConstantIntVal c1v ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c1Attr, hC1⟩ := Option.isSome_iff_exists.mp hC1Some
  rw [hC1] at hpattern
  simp only [] at hpattern
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, addType, hAddResType, hAddOperand0Type, hAddOperand1Type⟩ :=
    OperationPtr.Verified.llvm_add opVerif hAddType
  have hSubValEq : subVal = (op.getOperands! ctx.raw)[0]! := by rw [hAddOperands]; rfl
  have hC2vEq : c2v = (op.getOperands! ctx.raw)[1]! := by rw [hAddOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = subVal := by
    rw [hSubValEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = c2v := by
    rw [hC2vEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hSubValType : (subVal.getType! ctx.raw).val = Attribute.integerType addType := by
    rw [← hOperand0, hAddOperand0Type]
  have hC2vType : (c2v.getType! ctx.raw).val = Attribute.integerType addType := by
    rw [← hOperand1, hAddOperand1Type]
  obtain ⟨subValVal, c2vVal, hSubValVal, hC2vVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .add)
      (srcFn := fun a b p => Data.LLVM.Int.add a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .add))
      opInBounds hAddType hAddNumResults hAddOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hSubValType hC2vType
  subst hCf
  obtain ⟨av, haVal, hSubValIs, haType, hDomA, haIn, aNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchSub_implies)
      OperationPtr.Verified.llvm_sub OperationPtr.Pure.llvm_sub
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchSub subInnerOp ctx.raw = some (a, c1v) by
        simp only [matchBinopNoProps, bind, Option.bind, hSub2])
      hC1 (by rw [hAddOperands]; simp) hSubValType
  have hSpEq : subInnerOp.getProperties! ctx.raw (.llvm .sub) = sInnerProps :=
    ((matchSub_implies hSub2).2.2.2).symm
  rw [hSpEq] at hSubValIs
  obtain rfl : subValVal
      = Data.LLVM.Int.sub av (Data.LLVM.Int.constant addType.bitwidth c1Attr.value)
          sInnerProps.nsw sInnerProps.nuw := by
    have := hSubValVal.symm.trans hSubValIs; simpa using this
  have hC2vConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC2 (by rw [hAddOperands]; simp) hC2vType
  obtain rfl : c2vVal = Data.LLVM.Int.constant addType.bitwidth c2Attr.value := by
    have := hC2vVal.symm.trans hC2vConst; simpa using this
  rw [haType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : addType.bitwidth = 64 ∨ addType.bitwidth = 32 := by omega
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  peelOpCreation! hpattern ctx₁ cfOp hCf hDomA hDomA₁
  peelOpCreation! hpattern ctx₂ addNewOp hAddNew hDomA₁ hDomA₂
  cleanupHpattern hpattern
  have hCfNeAdd : cfOp ≠ addNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have haTypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType addType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have haTypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType addType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCf haIn]; exact haTypeAttr
  have hCfType : cfOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := cfOp)]
  have hCfOperands : cfOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCf (operation := cfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := cfOp)]
  have hCfProps : (cfOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨c2Attr.value - c1Attr.value, addType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCf (operation := cfOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hCfNeAdd, h1]
  have hCfResTypes : cfOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType addType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCf (operation := cfOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := cfOp)
    rw [if_neg hCfNeAdd] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) haTypeAttr
  have hAddNewType : addNewOp.getOpType! ctx₂.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewOperands : addNewOp.getOperands! ctx₂.raw
      = #[a, ValuePtr.opResult (cfOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewProps : addNewOp.getProperties! ctx₂.raw (.llvm .add) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewResTypes : addNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType addType, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := addNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) haTypeAttr₁
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      hDomA hDomA₂ aNotOp
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCfType hCfProps hCfOperands hCfResTypes
  have haVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int addType.bitwidth at') := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cfOp hCf))]
    exact haVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.add x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddNewType hAddNewProps hAddNewOperands hAddNewResTypes haVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int addType.bitwidth
      (Data.LLVM.Int.add at' (Data.LLVM.Int.constant addType.bitwidth
        (c2Attr.value - c1Attr.value)) false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.AMinusC1PlusC2 hWidth)
    (Data.LLVM.Int.add_mono _ _ _ _ haRef (isRefinedBy_refl _) false false)

/-! ### Sub{S,U}{max,min}Sub :  0 - minmax(a, 0 - a) → oppositeMinMax(a, 0 - a)

  Three-level, two-branch DAG match: the outer `sub` matches a `min`/`max` whose first operand
  reappears (as `a`) and whose second operand is a defining `sub 0 a`. Both zero operands are
  pinned to `0` through `EquationLemmaAt`. See `subNegMinMaxLocal` in `Combine.lean`. -/

set_option maxHeartbeats 1000000 in
/-- `matchBinop_getVar?` recovering a defining binop reached *not* directly through an operand of
    `op` but through a chain of dominating ops: the operand-membership hypothesis is replaced by a
    ready-made `binOp.strictlyDominates op` plus `base.InBounds`. -/
private theorem matchBinop_getVar?_of_strictlyDominates {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        match? opp c = some (l, r) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerBinop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (srcFn a b props)], mem, none)))
    {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base x y : ValuePtr} {binOp : OperationPtr} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some binOp)
    (hMatch : match? binOp ctx.raw = some (x, y))
    (hBaseIn : base.InBounds ctx.raw)
    (hBinSDom : binOp.strictlyDominates op ctx)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv yv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yv) ∧
      state.variables.getVar? base = some (RuntimeValue.int intType.bitwidth
        (srcFn xv yv (binOp.getProperties! ctx.raw (.llvm srcOp)))) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      (y.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧ y.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧ y.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw ∧ y ∉ op.getResults! ctx.raw := by
  obtain ⟨hBinType, hBinNumResults, hBinOperands⟩ := hMatchImplies hMatch
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hBinOpEq : basePtr.op = binOp := by simp [getDefiningOp] at hDef; grind
  subst hBinOpEq
  have hBinOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hBinVerified : basePtr.op.Verified ctx hBinOpIn := by grind
  obtain ⟨-, -, -, -, binIntType, hBinResType, hBinOperand0Type, hBinOperand1Type⟩ :=
    hVerified hBinVerified hBinType
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  have hIntTypeEq : intType = binIntType := by
    rw [hBaseTypeEq, hBinResType] at hBaseType; grind
  subst hIntTypeEq
  have hxIdxEq : x = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hBinOperands]; rfl
  have hyIdxEq : y = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hBinOperands]; rfl
  have hBinOperand0 : basePtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hBinOperand1 : basePtr.op.getOperand! ctx.raw 1 = y := by
    rw [hyIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hBinOperand0, hBinOperand0Type]
  have hyType : (y.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hBinOperand1, hBinOperand1Type]
  have hBinDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hBinPure : basePtr.op.Pure ctx.raw := hPure hBinType
  obtain ⟨cfB, hInterpBin⟩ := stateWf basePtr.op hBinOpIn hBinPure hBinDomIp
  obtain ⟨xv, yv, hxVal, hyVal, -, hBinResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := srcOp) (srcFn := srcFn)
      (props := basePtr.op.getProperties! ctx.raw (.llvm srcOp))
      hBinOpIn hBinType hBinNumResults hBinOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res h
          rw [hSemSrc bw a b props resultTypes blockOperands mem] at h
          injection h with h; injection h with h; exact h.symm)
      hInterpBin hxType hyType
  refine ⟨xv, yv, hxVal, hyVal, ?_, hxType, hyType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBaseEq, hBinResVal]; rfl
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hBinOpIn (by grind [OperationPtr.getOperands!])) hBinSDom
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hBinOpIn (by grind [OperationPtr.getOperands!])) hBinSDom
  · grind [OperationPtr.getOperands!]
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hBinSDom) x
      (by grind [OperationPtr.getOperands!])
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hBinSDom) y
      (by grind [OperationPtr.getOperands!])

/-- Turn a syntactic `getDefiningOp v = some d` for a single-result op into the
    well-formedness-backed `v.getDefiningOp! = some d`. -/
private theorem getDefiningOp!_of_getDefiningOp {ctx : WfIRContext OpCode}
    {v : ValuePtr} {d : OperationPtr}
    (hDef : getDefiningOp v ctx.raw = some d) (hVIn : v.InBounds ctx.raw)
    (hNumRes : d.getNumResults! ctx.raw = 1) :
    v.getDefiningOp! ctx.raw = some d := by
  obtain ⟨p, rfl⟩ : ∃ q, v = ValuePtr.opResult q := by
    cases v with
    | opResult q => exact ⟨q, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hpop : p.op = d := by simp [getDefiningOp] at hDef; grind
  subst hpop
  have hDIn : p.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : p.index < p.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hEq : p = p.op.getResult 0 := by
    have hidx : p.index = 0 := by omega
    cases p
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hOwner := (ctx.wellFormed.operations p.op hDIn).result_owner 0 (by grind)
  grind [ValuePtr.getDefiningOp!]

set_option maxHeartbeats 1000000 in
/-- Recover the runtime value of a matched constant-zero operand `z` of a container op that
    strictly dominates `op` (via `hToOp`), pinning it to `constant 0`. -/
private theorem matchConstantZero_getVar? {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op container : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {z : ValuePtr} {intType : IntegerType}
    (hZero : matchConstantZero z ctx.raw = some z)
    (hZMem : z ∈ container.getOperands! ctx.raw)
    (hZIn : z.InBounds ctx.raw)
    (hToOp : ∀ (d : OperationPtr), d.strictlyDominates container ctx → d.strictlyDominates op ctx)
    (hZType : (z.getType! ctx.raw).val = Attribute.integerType intType) :
    state.variables.getVar? z
      = some (RuntimeValue.int intType.bitwidth (Data.LLVM.Int.constant intType.bitwidth 0)) := by
  obtain ⟨-, attr, hCstVal, hAttrZero⟩ := matchConstantZero_implies hZero
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hCstVal
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    rw [← heq]; exact Subtype.ext hZType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCstSDomContainer : cstPtr.op.strictlyDominates container ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hCstDefines hZMem
  have hCstSDom : cstPtr.op.strictlyDominates op ctx := hToOp _ hCstSDomContainer
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType hInterpCst
  rw [hCstEq, hCstResVal, hAttrZero]

set_option maxHeartbeats 1000000 in
/-- Recovery skeleton for the four `Sub{S,U}{max,min}Sub` combines: peels the outer `sub`, recovers
    the min/max value (`mmFn`) and the inner `sub 0 a`'s value through the DAG, pins both zeros to
    `0`, and exposes the matched op's value
    `sub 0 (mmFn av (sub 0 av ins inu)) sProps.nsw sProps.nuw`. -/
private theorem subNegMinMax_core {mmOp : Llvm}
    {mmFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {matchMinMax : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    (hMMImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        matchMinMax opp c = some (l, r) →
        opp.getOpType! c = .llvm mmOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hMMVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm mmOp → opp.IsVerifiedIntegerBinop c)
    (hMMPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm mmOp → opp.Pure c)
    (hMMSem : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm mmOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' mmOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (mmFn a b)], mem, none)))
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {newState : InterpreterState ctx} {cf}
    {zeroOuter mmV a subV zeroInner a2 : ValuePtr}
    {dMM dSub : OperationPtr} {sProps innerProps : propertiesOf (.llvm .sub)}
    {intType : IntegerType}
    (hMatch : matchSub op ctx.raw = some (zeroOuter, mmV, sProps))
    (hZeroOuter : matchConstantZero zeroOuter ctx.raw = some zeroOuter)
    (hDefMM : getDefiningOp mmV ctx.raw = some dMM)
    (hMatchMM : matchMinMax dMM ctx.raw = some (a, subV))
    (hDefSub : getDefiningOp subV ctx.raw = some dSub)
    (hMatchSub : matchSub dSub ctx.raw = some (zeroInner, a2, innerProps))
    (hZeroInner : matchConstantZero zeroInner ctx.raw = some zeroInner)
    (ha2 : a2 = a)
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType)
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ (av : Data.LLVM.Int intType.bitwidth) (ins inu : Bool),
      state.variables.getVar? a = some (RuntimeValue.int intType.bitwidth av) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.sub (Data.LLVM.Int.constant intType.bitwidth 0)
          (mmFn av (Data.LLVM.Int.sub (Data.LLVM.Int.constant intType.bitwidth 0) av ins inu))
          sProps.nsw sProps.nuw)) ∧
      cf = none ∧
      (a.getType! ctx.raw).val = Attribute.integerType intType ∧
      a.dominatesIp (InsertPoint.before op) ctx ∧ a.InBounds ctx.raw ∧
      a ∉ op.getResults! ctx.raw := by
  -- Outer sub structural facts.
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchSub_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subIntType, hSubResType, hSubOp0Type, hSubOp1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hOpType
  have hIntTypeEq : intType = subIntType := by rw [hSubResType] at hResType; grind
  subst hIntTypeEq
  have hzoEq : zeroOuter = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hmmEq : mmV = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = zeroOuter := by
    rw [hzoEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = mmV := by
    rw [hmmEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hzoType : (zeroOuter.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hSubOp0Type]
  have hmmType : (mmV.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hSubOp1Type]
  have hmmMem : mmV ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  have hzoMem : zeroOuter ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  -- Unfold the outer sub's interpretation.
  obtain ⟨zov, mmv, hzoVal, hmmVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res h
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at h
          grind)
      hinterp hzoType hmmType
  -- Recover the min/max value through `mmV`.
  obtain ⟨av, sv, haVal, hsubVVal, hmmResVal, haType, hsubVType, haDom, hsubVDom, haIn, hsubVIn,
      haNotRes, hsubVNotRes⟩ :=
    matchBinop_getVar?_of_EquationLemmaAt (srcOp := mmOp) (srcFn := fun a b _ => mmFn a b)
      hMMImplies hMMVerified hMMPure hMMSem ctxDom ctxVerif opInBounds stateWf hDefMM hMatchMM
      hmmMem hmmType
  obtain rfl : mmv = mmFn av sv := by have := hmmVal.symm.trans hmmResVal; simpa using this
  -- `dMM` and `dSub` strictly dominate `op`.
  have hmmIn : mmV.InBounds ctx.raw := by grind
  obtain ⟨hMMType, hMMnr, hMMOperands⟩ := hMMImplies hMatchMM
  have hmmDefines : mmV.getDefiningOp! ctx.raw = some dMM :=
    getDefiningOp!_of_getDefiningOp hDefMM hmmIn hMMnr
  have hDMMSDom : dMM.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hmmDefines hmmMem
  have hsubVMem : subV ∈ dMM.getOperands! ctx.raw := by rw [hMMOperands]; simp
  obtain ⟨hSubOpType, hSubnr, hSubOperands, -⟩ := matchSub_implies hMatchSub
  have hsubVDefines : subV.getDefiningOp! ctx.raw = some dSub :=
    getDefiningOp!_of_getDefiningOp hDefSub hsubVIn hSubnr
  have hDSubSDomMM : dSub.strictlyDominates dMM ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hsubVDefines hsubVMem
  have hDSubSDom : dSub.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hDSubSDomMM hDMMSDom
  -- Recover the inner sub's value through `subV`.
  have hMatchNoProps : matchBinopNoProps matchSub dSub ctx.raw = some (zeroInner, a2) := by
    simp [matchBinopNoProps, bind, Option.bind, hMatchSub]
  obtain ⟨ziv, a2v, hziVal, ha2Val, hsubResVal, hziType, ha2Type, hziDom, ha2Dom, hziIn, ha2In,
      hziNotRes, ha2NotRes⟩ :=
    matchBinop_getVar?_of_strictlyDominates (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (matchBinopNoProps_implies matchSub_implies) OperationPtr.Verified.llvm_sub
      (fun h => OperationPtr.Pure.llvm_sub h)
      (by intro bw a b props rt bo mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDefSub
      hMatchNoProps hsubVIn hDSubSDom hsubVType
  -- Pin both zeros to `0`, and collapse `a2` into `a`.
  have hziZero : state.variables.getVar? zeroInner
      = some (RuntimeValue.int intType.bitwidth (Data.LLVM.Int.constant intType.bitwidth 0)) :=
    matchConstantZero_getVar? ctxDom ctxVerif opInBounds stateWf hZeroInner
      (by rw [hSubOperands]; simp) hziIn
      (fun d hd => OperationPtr.strictlyDominates_trans hd hDSubSDom) hziType
  obtain rfl : ziv = Data.LLVM.Int.constant intType.bitwidth 0 := by
    have := hziVal.symm.trans hziZero; simpa using this
  have hzoZero : state.variables.getVar? zeroOuter
      = some (RuntimeValue.int intType.bitwidth (Data.LLVM.Int.constant intType.bitwidth 0)) :=
    matchConstantZero_getVar? ctxDom ctxVerif opInBounds stateWf hZeroOuter hzoMem
      (by grind) (fun _ hd => hd) hzoType
  obtain rfl : zov = Data.LLVM.Int.constant intType.bitwidth 0 := by
    have := hzoVal.symm.trans hzoZero; simpa using this
  have ha2vEq : a2v = av := by
    have h2 : state.variables.getVar? a = some (RuntimeValue.int intType.bitwidth a2v) := by
      rw [← ha2]; exact ha2Val
    have := h2.symm.trans haVal; simpa using this
  obtain rfl : sv = Data.LLVM.Int.sub (Data.LLVM.Int.constant intType.bitwidth 0) av
      (dSub.getProperties! ctx.raw (.llvm .sub)).nsw
      (dSub.getProperties! ctx.raw (.llvm .sub)).nuw := by
    have h := hsubVVal.symm.trans hsubResVal
    rw [ha2vEq] at h
    simpa using h
  refine ⟨av, (dSub.getProperties! ctx.raw (.llvm .sub)).nsw,
    (dSub.getProperties! ctx.raw (.llvm .sub)).nuw, haVal, hMem, ?_, hCf, haType, haDom, haIn,
    haNotRes⟩
  rw [hRes, hProps]

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for the four `Sub{S,U}{max,min}Sub` combines. Parameterized over the
    inner min/max op (`mmOp`/`mmFn` + matcher/verifier/purity/semantics facts), the emitted min/max
    op (`dst`/`dstFn`/`dprops` + semantics `hDstSem` and monotonicity `hDstMono`), and the data
    refinement lemma `hRefine` (at `i64`). -/
theorem subNegMinMaxLocal_preservesSemantics {mmOp dst : Llvm}
    {mmFn dstFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw}
    {matchMinMax : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr)}
    {dprops : propertiesOf (.llvm dst)}
    (hMMImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {l r},
        matchMinMax opp c = some (l, r) →
        opp.getOpType! c = .llvm mmOp ∧ opp.getNumResults! c = 1 ∧ opp.getOperands! c = #[l, r])
    (hMMVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm mmOp → opp.IsVerifiedIntegerBinop c)
    (hMMPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm mmOp → opp.Pure c)
    (hMMSem : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm mmOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' mmOp props rt #[.int bw a, .int bw b] bo mem
          = some (.ok (#[.int bw (mmFn a b)], mem, none)))
    (hDstSem : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (rt : Array TypeAttr)
        (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' dst dprops rt #[.int bw x, .int bw y] bo mem
          = some (.ok (#[.int bw (dstFn x y)], mem, none)))
    (hDstMono : ∀ {bw : Nat} (x₁ x₂ y₁ y₂ : Data.LLVM.Int bw), x₁ ⊒ y₁ → x₂ ⊒ y₂ →
        dstFn x₁ x₂ ⊒ dstFn y₁ y₂)
    (hRefine : ∀ {w : Nat}, w = 64 → ∀ (av : Data.LLVM.Int w) (ins inu ons onu : Bool),
        Data.LLVM.Int.sub (Data.LLVM.Int.constant w 0)
            (mmFn av (Data.LLVM.Int.sub (Data.LLVM.Int.constant w 0) av ins inu)) ons onu
          ⊒ dstFn av (Data.LLVM.Int.sub (Data.LLVM.Int.constant w 0) av false false))
    {h : LocalRewritePattern.ReturnOps (subNegMinMaxLocal matchMinMax dst dprops)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (subNegMinMaxLocal matchMinMax dst dprops)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (subNegMinMaxLocal matchMinMax dst dprops)}
    {h₄ : LocalRewritePattern.ReturnValues (subNegMinMaxLocal matchMinMax dst dprops)} :
    LocalRewritePattern.PreservesSemantics (subNegMinMaxLocal matchMinMax dst dprops) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, subNegMinMaxLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨zeroOuter, mmV, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel `matchConstantZero zeroOuter`.
  have hZOSome : (matchConstantZero zeroOuter ctx.raw).isSome := by
    cases hM : matchConstantZero zeroOuter ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨zoRes, hZeroOuterRaw⟩ := Option.isSome_iff_exists.mp hZOSome
  obtain rfl : zoRes = zeroOuter := (matchConstantZero_implies hZeroOuterRaw).1
  rw [hZeroOuterRaw] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp mmV`.
  have hDefMMSome : (getDefiningOp mmV ctx.raw).isSome := by
    cases hM : getDefiningOp mmV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dMM, hDefMM⟩ := Option.isSome_iff_exists.mp hDefMMSome
  rw [hDefMM] at hpattern
  simp only [] at hpattern
  -- Peel `matchMinMax dMM`.
  have hMMSome : (matchMinMax dMM ctx.raw).isSome := by
    cases hM : matchMinMax dMM ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, subV⟩, hMatchMM⟩ := Option.isSome_iff_exists.mp hMMSome
  rw [hMatchMM] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp subV`.
  have hDefSubSome : (getDefiningOp subV ctx.raw).isSome := by
    cases hM : getDefiningOp subV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dSub, hDefSub⟩ := Option.isSome_iff_exists.mp hDefSubSome
  rw [hDefSub] at hpattern
  simp only [] at hpattern
  -- Peel the inner `matchSub`.
  have hMatchSubSome : (matchSub dSub ctx.raw).isSome := by
    cases hM : matchSub dSub ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨zeroInner, a2, innerProps⟩, hMatchSub⟩ := Option.isSome_iff_exists.mp hMatchSubSome
  rw [hMatchSub] at hpattern
  simp only [] at hpattern
  -- Peel `matchConstantZero zeroInner`.
  have hZISome : (matchConstantZero zeroInner ctx.raw).isSome := by
    cases hM : matchConstantZero zeroInner ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨ziRes, hZeroInnerRaw⟩ := Option.isSome_iff_exists.mp hZISome
  obtain rfl : ziRes = zeroInner := (matchConstantZero_implies hZeroInnerRaw).1
  rw [hZeroInnerRaw] at hpattern
  simp only [] at hpattern
  -- Peel the `a2 = a` guard.
  have ha2 : a2 = a := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos ha2] at hpattern
  -- Type/width guard on `a`.
  obtain ⟨aty, hAtyType⟩ : ∃ t, (a.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (a.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hAtyType] at hpattern
  simp only [] at hpattern
  have hWidth64 : aty.bitwidth = 64 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hWidth64] at hpattern
  -- `op`'s result type is an integer type (from the `sub` verifier).
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntTy, hOpResTy, -, -⟩ := OperationPtr.Verified.llvm_sub opVerif hOpType
  have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntTy := by
    rw [hOpResTy]
  -- Recover the matched op's value and `a`'s facts.
  obtain ⟨av, ins, inu, haVal, hMem, hResVal, hCf, haType, haDom, haIn, haNotRes⟩ :=
    subNegMinMax_core hMMImplies hMMVerified hMMPure hMMSem ctxDom ctxVerif opInBounds stateWf
      hMatch hZeroOuterRaw hDefMM hMatchMM hDefSub hMatchSub hZeroInnerRaw ha2 hResType hinterp
  subst hCf
  -- `opIntTy = aty`, so collapse the two and read off the width.
  obtain rfl : opIntTy = aty := by
    have h := haType.symm.trans hAtyType; injection h
  have hIntBw : opIntTy.bitwidth = 64 := hWidth64
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the three creations: constant, sub, min/max.
  peelOpCreation! hpattern ctx₁ c0Op hC0 haDom haDom₁
  peelOpCreation! hpattern ctx₂ subOp hSub haDom₁ haDom₂
  peelOpCreation! hpattern ctx₃ mmOp2 hMM haDom₂ haDom₃
  cleanupHpattern hpattern
  -- Distinctness of the three created ops.
  have hC0NeSub : c0Op ≠ subOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hC0NeMM : c0Op ≠ mmOp2 := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hSubNeMM : subOp ≠ mmOp2 := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `a`'s type as a `TypeAttr`, transported to each ctx.
  have hATypeAttr : a.getType! ctx.raw
      = (⟨Attribute.integerType opIntTy, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext haType
  have hATypeAttr₁ : a.getType! ctx₁.raw
      = (⟨Attribute.integerType opIntTy, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC0 haIn]; exact hATypeAttr
  -- Structural facts for the constant.
  have hC0Type : c0Op.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := c0Op),
      OperationPtr.getOpType!_WfRewriter_createOp hMM (operation := c0Op)]
  have hC0Operands : c0Op.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hC0 (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := c0Op),
      OperationPtr.getOperands!_WfRewriter_createOp hMM (operation := c0Op)]
  have hC0Props : (c0Op.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨0, opIntTy⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hC0 (operation := c0Op)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hMM hC0NeMM,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSub hC0NeSub, h1]
  have hC0ResTypes : c0Op.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntTy, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hC0 (operation := c0Op)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := c0Op)
    rw [if_neg hC0NeSub] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hMM (operation := c0Op)
    rw [if_neg hC0NeMM] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hATypeAttr
  -- Structural facts for the sub.
  have hSubType : subOp.getOpType! ctx₃.raw = .llvm .sub := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMM (operation := subOp)]
  have hSubOperands : subOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (c0Op.getResult 0), a] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMM (operation := subOp)]
  have hSubProps : subOp.getProperties! ctx₃.raw (.llvm .sub) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hSub (operation := subOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hMM hSubNeMM]
  have hSubResTypes : subOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntTy, haType ▸ (a.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSub (operation := subOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hMM (operation := subOp)
    rw [if_neg hSubNeMM] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hATypeAttr₁
  -- Structural facts for the emitted min/max. Its result type is `op`'s result type.
  have hMMType : mmOp2.getOpType! ctx₃.raw = .llvm dst := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hMM (operation := mmOp2)]
  have hMMOperands : mmOp2.getOperands! ctx₃.raw
      = #[a, ValuePtr.opResult (subOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMM (operation := mmOp2)]
  have hMMProps : mmOp2.getProperties! ctx₃.raw (.llvm dst) = dprops := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hMM (operation := mmOp2)]
  have hOpResTypeAttr : ((op.getResult 0).get! ctx.raw).type
      = (⟨Attribute.integerType opIntTy,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := Subtype.ext hResType
  have hOpResGetType : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType opIntTy,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact hOpResTypeAttr
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hResVal
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hOpRes0In₁ : (ValuePtr.opResult (op.getResult 0)).InBounds ctx₁.raw :=
    WfRewriter.createOp_inBounds_mono (ptr := .value (ValuePtr.opResult (op.getResult 0)))
      hC0 hOpRes0In
  have hOpResGetType₂ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
      = (⟨Attribute.integerType opIntTy,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hSub hOpRes0In₁,
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hC0 hOpRes0In]
    exact hOpResGetType
  have hMMResTypes : mmOp2.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType opIntTy,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hMM (operation := mmOp2)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hOpResGetType₂
  have hSubNumRes : subOp.getNumResults! ctx₂.raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hSub (operation := subOp), if_pos rfl]; rfl
  have hSubResIn : (ValuePtr.opResult (subOp.getResult 0)).InBounds ctx₂.raw := by
    have hnr := hSubNumRes
    clear valueRefinement state'Dom state'Wf hpattern hResVal
    rw [ValuePtr.inBounds_opResult]
    refine ⟨WfRewriter.createOp_new_inBounds subOp hSub, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  -- Read the refined `a` in the target state.
  obtain ⟨atv, hAVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haVal
      haDom haDom₃ haNotRes
  -- Replay the constant, then the sub, then the min/max.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hC0Type hC0Props hC0Operands hC0ResTypes
  have hAVal₁ : s₁.variables.getVar? a = some (RuntimeValue.int opIntTy.bitwidth atv) := by
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds c0Op hC0))]
    exact hAVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun x y => Data.LLVM.Int.sub x y false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hSubType hSubProps hSubOperands hSubResTypes hRes₁ hAVal₁
  have hAVal₂ : s₂.variables.getVar? a = some (RuntimeValue.int opIntTy.bitwidth atv) := by
    rw [hFrame₂ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      (WfRewriter.createOp_inBounds_mono (ptr := .value a) hC0 haIn)
      (WfRewriter.createOp_new_not_inBounds subOp hSub))]
    exact hAVal₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₂) (inBounds := by grind)
      (f := fun x y => dstFn x y)
      (by intro resultTypes blockOperands mem; exact hDstSem _ _ _ _ _ _)
      hMMType hMMProps hMMOperands hMMResTypes hAVal₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int opIntTy.bitwidth
      (dstFn atv (Data.LLVM.Int.sub (Data.LLVM.Int.constant opIntTy.bitwidth 0) atv false false))],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (hRefine hIntBw av ins inu sProps.nsw sProps.nuw)
    (hDstMono av (Data.LLVM.Int.sub (Data.LLVM.Int.constant opIntTy.bitwidth 0) av false false)
      atv (Data.LLVM.Int.sub (Data.LLVM.Int.constant opIntTy.bitwidth 0) atv false false)
      haRef (Data.LLVM.Int.sub_mono _ _ _ _ (isRefinedBy_refl _) haRef false false))

/-! The four instantiations. -/

theorem SubSmaxSub_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (subNegMinMaxLocal matchSmax .intr__smin ()) h h₂ h₃ h₄ :=
  subNegMinMaxLocal_preservesSemantics (mmFn := fun a b => Data.LLVM.Int.smax a b)
    (dstFn := fun a b => Data.LLVM.Int.smin a b)
    (fun hMatch => matchSmax_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__smax opVerif hOpType)
    (fun hType => OperationPtr.Pure.llvm_intr__smax hType)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw av ins inu ons onu => by subst hw; exact Data.LLVM.Int.SubSmaxSub_rw)

theorem SubUmaxSub_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (subNegMinMaxLocal matchUmax .intr__umin ()) h h₂ h₃ h₄ :=
  subNegMinMaxLocal_preservesSemantics (mmFn := fun a b => Data.LLVM.Int.umax a b)
    (dstFn := fun a b => Data.LLVM.Int.umin a b)
    (fun hMatch => matchUmax_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__umax opVerif hOpType)
    (fun hType => OperationPtr.Pure.llvm_intr__umax hType)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umin_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw av ins inu ons onu => by subst hw; exact Data.LLVM.Int.SubUmaxSub_rw)

theorem SubSminSub_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (subNegMinMaxLocal matchSmin .intr__smax ()) h h₂ h₃ h₄ :=
  subNegMinMaxLocal_preservesSemantics (mmFn := fun a b => Data.LLVM.Int.smin a b)
    (dstFn := fun a b => Data.LLVM.Int.smax a b)
    (fun hMatch => matchSmin_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__smin opVerif hOpType)
    (fun hType => OperationPtr.Pure.llvm_intr__smin hType)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.smax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw av ins inu ons onu => by subst hw; exact Data.LLVM.Int.SubSminSub_rw)

theorem SubUminSub_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (subNegMinMaxLocal matchUmin .intr__umax ()) h h₂ h₃ h₄ :=
  subNegMinMaxLocal_preservesSemantics (mmFn := fun a b => Data.LLVM.Int.umin a b)
    (dstFn := fun a b => Data.LLVM.Int.umax a b)
    (fun hMatch => matchUmin_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__umin opVerif hOpType)
    (fun hType => OperationPtr.Pure.llvm_intr__umin hType)
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x₁ x₂ y₁ y₂ h₁ h₂ => Data.LLVM.Int.umax_mono x₁ x₂ y₁ y₂ h₁ h₂)
    (fun hw av ins inu ons onu => by subst hw; exact Data.LLVM.Int.SubUminSub_rw)

/-! ### funnel_shift_{left,right}_zero :  `fshl x y 0 → x` ,  `fshr x y 0 → y`

  Both keep a data operand of a funnel shift whose amount matched the constant `0`, creating no
  operations. Shared combinator proof `funnelShiftZeroLocal_preservesSemantics`, mirroring
  `binopZeroLeftLocal_preservesSemantics` but on a *ternary* source op: the source is unfolded with
  `matchTernaryOp_interpretOp_unfold`, verified via `IsVerifiedIntegerTernop`, and the matched
  constant sits on operand 2 (the shift amount). The kept operand (`a` for `fshl`, `b` for `fshr`,
  selected by `keepFirst`) is a dominating, non-result operand, so its refinement transports through
  the `interpretOpList [] state'` no-op to close the simulation. The data core is
  `fshl_zero_amt`/`fshr_zero_amt`. -/
set_option maxHeartbeats 1000000 in
theorem funnelShiftZeroLocal_preservesSemantics {srcOp : Llvm}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr)}
    {keepFirst : Bool}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw →
      Data.LLVM.Int bw}
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
    (hRefine : ∀ {bw : Nat} (x y : Data.LLVM.Int bw),
        srcFn x y (Data.LLVM.Int.constant bw 0) ⊒ (bif keepFirst then x else y))
    {h : LocalRewritePattern.ReturnOps (funnelShiftZeroLocal match? keepFirst)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (funnelShiftZeroLocal match? keepFirst)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (funnelShiftZeroLocal match? keepFirst)}
    {h₄ : LocalRewritePattern.ReturnValues (funnelShiftZeroLocal match? keepFirst)} :
    LocalRewritePattern.PreservesSemantics (funnelShiftZeroLocal match? keepFirst) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, funnelShiftZeroLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the ternary match.
  have hMatchSome : (match? op ctx.raw).isSome := by
    cases hM : match? op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, amt⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands⟩ := hMatchImplies hMatch
  -- Result-type guard: the result must be an integer.
  obtain ⟨intTypeRes, hResTypeRes⟩ :
      ∃ intType, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResTypeRes] at hpattern
  simp only [] at hpattern
  -- Constant match on the shift amount `amt`.
  have hCstSome : (matchConstantIntVal amt ctx.raw).isSome := by
    cases hM : matchConstantIntVal amt ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cst, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  -- The `value = 0` guard (the initial `simp` swapped the negated `if`).
  have hVal0 : cst.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hVal0] at hpattern
  -- Structural facts from the verifier.
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type, hOp2Type⟩ :=
    hVerified opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [show a = (op.getOperands! ctx.raw)[0]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [show b = (op.getOperands! ctx.raw)[1]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand2 : op.getOperand! ctx.raw 2 = amt := by
    rw [show amt = (op.getOperands! ctx.raw)[2]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hAmtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand2, hOp2Type]
  -- Unfold the source interpretation: exposes `a`, `b`, `amt`'s values and `srcFn xa xb xc`.
  obtain ⟨xa, xb, xc, haVal, hbVal, hcVal, hMem, hRes, hCf⟩ :=
    matchTernaryOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hSemSrc
      hinterp hAType hBType hAmtType
  subst hCf
  -- Pin the shift amount's runtime value to `constant _ 0`.
  have hamtVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hAmtType
  have hxcEq : xc = Data.LLVM.Int.constant intType.bitwidth cst.value := by
    have := hcVal.symm.trans hamtVal; simpa using this
  rw [hVal0] at hxcEq
  subst hxcEq
  -- The kept operand `K = bif keepFirst then a else b` is an operand of `op`.
  have hKeptMem : (bif keepFirst then a else b) ∈ op.getOperands! ctx.raw := by
    rw [hOperands]; cases keepFirst <;> simp
  have hDomKept : (bif keepFirst then a else b).dominatesIp (InsertPoint.before op) ctx :=
    ctxDom.operand_dominates_op opInBounds hKeptMem
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have kNotOp : ¬ (bif keepFirst then a else b) ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Nothing is created: `newCtx = ctx`, `newOps = #[]`, `newValues = #[K]`.
  obtain ⟨rfl, rfl, rfl⟩ :
      newCtx = ctx ∧ newOps = #[] ∧ newValues = #[bif keepFirst then a else b] := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hpattern; grind
  -- The kept operand's runtime value in the source state.
  have hKeptVal : state.variables.getVar? (bif keepFirst then a else b)
      = some (RuntimeValue.int intType.bitwidth (bif keepFirst then xa else xb)) := by
    cases keepFirst <;> simp [haVal, hbVal]
  obtain ⟨kt, hKVal', hktRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hKeptVal
      hDomKept hDomKept kNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.int intType.bitwidth kt], by simp [hKVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  refine isRefinedBy_trans ?_ hktRef
  have := hRefine (bw := intType.bitwidth) xa xb
  cases keepFirst <;> simpa using this

theorem funnel_shift_left_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps funnel_shift_left_zero_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges funnel_shift_left_zero_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds funnel_shift_left_zero_local}
    {h₄ : LocalRewritePattern.ReturnValues funnel_shift_left_zero_local} :
    LocalRewritePattern.PreservesSemantics funnel_shift_left_zero_local h h₂ h₃ h₄ :=
  funnelShiftZeroLocal_preservesSemantics (srcOp := .intr__fshl)
    (match? := matchFshl) (keepFirst := true)
    (srcFn := fun x y z => Data.LLVM.Int.fshl x y z)
    matchFshl_implies
    OperationPtr.Verified.llvm_intr__fshl
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x y => Data.LLVM.Int.fshl_zero_amt (x := x) (y := y))

theorem funnel_shift_right_zero_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps funnel_shift_right_zero_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges funnel_shift_right_zero_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds funnel_shift_right_zero_local}
    {h₄ : LocalRewritePattern.ReturnValues funnel_shift_right_zero_local} :
    LocalRewritePattern.PreservesSemantics funnel_shift_right_zero_local h h₂ h₃ h₄ :=
  funnelShiftZeroLocal_preservesSemantics (srcOp := .intr__fshr)
    (match? := matchFshr) (keepFirst := false)
    (srcFn := fun x y z => Data.LLVM.Int.fshr x y z)
    matchFshr_implies
    OperationPtr.Verified.llvm_intr__fshr
    (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
    (fun x y => Data.LLVM.Int.fshr_zero_amt (x := x) (y := y))

/-! ### sub_of_mul_const :  sub a (mul x C) → add a (mul x (-C))   (C constant)

  A two-level DAG match (the outer `sub`'s second operand is a defining `mul` whose second operand
  is a matched integer constant) that creates *three* ops: a fresh `llvm.mlir.constant (-C)`, a new
  `mul x (-C)`, and an `add a (...)`. Combines the DAG-match/folded-constant machinery of the
  constant-reassociation combines (`matchBinopSndConst_getVar?_of_EquationLemmaAt`,
  `interpretOp_llvm_constant_forward`) with the three-creation replay of `narrowBinopLocal`. The
  created `mul` and `add` both clear their `nsw`/`nuw` flags (see the flag note in `Combine.lean`
  and the counterexample recorded on `Data.LLVM.Int.SubMulConst` in `LLVMProofs.lean`); the matched
  ops' flags (`mProps` on the `mul`, `op`'s props on the `sub`) stay free. The width is generic —
  the data lemma is a width-independent ring identity — so there is no bitwidth guard or split. -/
set_option maxHeartbeats 1000000 in
theorem sub_of_mul_const_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sub_of_mul_const_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sub_of_mul_const_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sub_of_mul_const_local}
    {h₄ : LocalRewritePattern.ReturnValues sub_of_mul_const_local} :
    LocalRewritePattern.PreservesSemantics sub_of_mul_const_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sub_of_mul_const_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[a, mulV]`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, mulV, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the defining `mul` of `mulV`, its operands `#[x, cval]`, and the constant `cval`.
  have hDefSome : (getDefiningOp mulV ctx.raw).isSome := by
    cases hM : getDefiningOp mulV ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨mulOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hMulSome : (matchMul mulOp ctx.raw).isSome := by
    cases hM : matchMul mulOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cval, mProps⟩, hMul⟩ := Option.isSome_iff_exists.mp hMulSome
  rw [hMul] at hpattern
  simp only [] at hpattern
  have hCSome : (matchConstantIntVal cval ctx.raw).isSome := by
    cases hM : matchConstantIntVal cval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cAttr, hC⟩ := Option.isSome_iff_exists.mp hCSome
  rw [hC] at hpattern
  simp only [] at hpattern
  -- Verifier facts for the outer `sub`: operands/result share type `subType`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hMulVEq : mulV = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = mulV := by
    rw [hMulVEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have haType : (a.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hMulVType : (mulV.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  -- `a`'s facts: it is the outer op's operand 0, so it dominates `before op`, is in bounds, and is
  -- not one of `op`'s results.
  have haMem : a ∈ op.getOperands! ctx.raw := by rw [hSubOperands]; simp
  have hDomA : a.dominatesIp (InsertPoint.before op) ctx :=
    ctxDom.operand_dominates_op opInBounds haMem
  have haIn : a.InBounds ctx.raw := by grind [OperationPtr.getOperands!]
  have aNotRes : a ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl a haMem
  -- Unfold the outer `sub`'s interpretation.
  obtain ⟨aVal, mulVal, haValVal, hMulValVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun p q pr => Data.LLVM.Int.sub p q pr.nsw pr.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw p q props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp haType hMulVType
  subst hCf
  -- Recover the defining `mul x (const c)`'s value (with `c` pinned), and `x`'s facts.
  obtain ⟨xv, hxVal, hMulVIs, hxType, hDomX, hxIn, xNotOp⟩ :=
    matchBinopSndConst_getVar?_of_EquationLemmaAt (srcOp := .mul)
      (srcFn := fun p q pr => Data.LLVM.Int.mul p q pr.nsw pr.nuw)
      (matchBinopNoProps_implies matchMul_implies)
      OperationPtr.Verified.llvm_mul OperationPtr.Pure.llvm_mul
      (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      ctxDom ctxVerif opInBounds stateWf hDef
      (show matchBinopNoProps matchMul mulOp ctx.raw = some (x, cval) by
        simp only [matchBinopNoProps, bind, Option.bind, hMul])
      hC (by rw [hSubOperands]; simp) hMulVType
  have hMpEq : mulOp.getProperties! ctx.raw (.llvm .mul) = mProps :=
    ((matchMul_implies hMul).2.2.2).symm
  rw [hMpEq] at hMulVIs
  -- Pin `mulVal`.
  obtain rfl : mulVal
      = Data.LLVM.Int.mul xv (Data.LLVM.Int.constant subType.bitwidth cAttr.value)
          mProps.nsw mProps.nuw := by
    have := hMulValVal.symm.trans hMulVIs; simpa using this
  -- Resolve the `.integerType xty` guard-let in `hpattern`.
  rw [hxType] at hpattern
  simp only [] at hpattern
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the three creations: `constant (-C)`, `mul x (-C)`, `add a (mul ..)`. Thread the
  -- dominance of the two live operands `a` and `x` through each.
  peelOpCreation!₂ hpattern ctx₁ cnOp hCn hDomA hDomA₁ hDomX hDomX₁
  peelOpCreation!₂ hpattern ctx₂ mulNewOp hMulNew hDomA₁ hDomA₂ hDomX₁ hDomX₂
  peelOpCreation!₂ hpattern ctx₃ addNewOp hAddNew hDomA₂ hDomA₃ hDomX₂ hDomX₃
  cleanupHpattern hpattern
  have hCnNeMul : cnOp ≠ mulNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hCnNeAdd : cnOp ≠ addNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hMulNeAdd : mulNewOp ≠ addNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `x`'s type as a `TypeAttr`, transported to each creation context.
  have hxTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hxTypeAttr₁ : x.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCn hxIn]; exact hxTypeAttr
  have hxTypeAttr₂ : x.getType! ctx₂.raw
      = (⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hMulNew
      (WfRewriter.createOp_inBounds_mono (ptr := .value x) hCn hxIn)]
    exact hxTypeAttr₁
  -- Structural facts for the fresh constant.
  have hCnType : cnOp.getOpType! ctx₃.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCn (operation := cnOp),
      OperationPtr.getOpType!_WfRewriter_createOp hMulNew (operation := cnOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := cnOp)]
  have hCnOperands : cnOp.getOperands! ctx₃.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCn (operation := cnOp),
      OperationPtr.getOperands!_WfRewriter_createOp hMulNew (operation := cnOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := cnOp)]
  have hCnProps : (cnOp.getProperties! ctx₃.raw (.llvm .mlir__constant)).value
      = .integer ⟨-cAttr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCn (operation := cnOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hCnNeAdd,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hMulNew hCnNeMul, h1]
  have hCnResTypes : cnOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCn (operation := cnOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hMulNew (operation := cnOp)
    rw [if_neg hCnNeMul] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := cnOp)
    rw [if_neg hCnNeAdd] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hxTypeAttr
  -- Structural facts for the new `mul`.
  have hMulNewType : mulNewOp.getOpType! ctx₃.raw = .llvm .mul := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hMulNew (operation := mulNewOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := mulNewOp)]
  have hMulNewOperands : mulNewOp.getOperands! ctx₃.raw
      = #[x, ValuePtr.opResult (cnOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMulNew (operation := mulNewOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := mulNewOp)]
  have hMulNewProps : mulNewOp.getProperties! ctx₃.raw (.llvm .mul)
      = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hMulNew (operation := mulNewOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hMulNeAdd]
  have hMulNewResTypes : mulNewOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hMulNew (operation := mulNewOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := mulNewOp)
    rw [if_neg hMulNeAdd] at hT3
    rw [hT3, hT]
    exact congrArg (fun t => #[t]) hxTypeAttr₁
  -- Structural facts for the new `add`.
  have hAddNewType : addNewOp.getOpType! ctx₃.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewOperands : addNewOp.getOperands! ctx₃.raw
      = #[a, ValuePtr.opResult (mulNewOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewProps : addNewOp.getProperties! ctx₃.raw (.llvm .add)
      = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewResTypes : addNewOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := addNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hxTypeAttr₂
  -- Read the refined `x` and `a` in the target state.
  obtain ⟨xt, hXVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₃ xNotOp
  obtain ⟨at', haVal', haRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom haIn haValVal
      hDomA hDomA₃ aNotRes
  -- Replay the constant, then the `mul`, then the `add`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state')
      (inBounds := WfRewriter.createOp_inBounds_mono (ptr := .operation cnOp) hAddNew
        (WfRewriter.createOp_inBounds_mono (ptr := .operation cnOp) hMulNew
          (WfRewriter.createOp_new_inBounds cnOp hCn)))
      hCnType hCnProps hCnOperands hCnResTypes
  have hXVal₁ : s₁.variables.getVar? x = some (RuntimeValue.int subType.bitwidth xt) := by
    rw [hFrame₁ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hxIn
      (WfRewriter.createOp_new_not_inBounds cnOp hCn))]
    exact hXVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁)
      (inBounds := WfRewriter.createOp_inBounds_mono (ptr := .operation mulNewOp) hAddNew
        (WfRewriter.createOp_new_inBounds mulNewOp hMulNew))
      (it := subType) (f := fun p q => Data.LLVM.Int.mul p q false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hMulNewType hMulNewProps hMulNewOperands hMulNewResTypes hXVal₁ hRes₁
  have haVal₂ : s₂.variables.getVar? a = some (RuntimeValue.int subType.bitwidth at') := by
    rw [hFrame₂ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
        (WfRewriter.createOp_inBounds_mono (ptr := .value a) hCn haIn)
        (WfRewriter.createOp_new_not_inBounds mulNewOp hMulNew))]
    rw [hFrame₁ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds haIn
      (WfRewriter.createOp_new_not_inBounds cnOp hCn))]
    exact haVal'
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₂)
      (inBounds := WfRewriter.createOp_new_inBounds addNewOp hAddNew)
      (it := subType) (f := fun p q => Data.LLVM.Int.add p q false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddNewType hAddNewProps hAddNewOperands hAddNewResTypes haVal₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.add at' (Data.LLVM.Int.mul xt
        (Data.LLVM.Int.constant subType.bitwidth (-cAttr.value)) false false) false false)],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `sub aVal (mul xv C ..) .. ⊒ add aVal (mul xv (-C) ..) .. ⊒ add at' (mul xt (-C) ..) ..`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans Data.LLVM.Int.SubMulConst
    (Data.LLVM.Int.add_mono _ _ _ _ haRef
      (Data.LLVM.Int.mul_mono _ _ _ _ hxRef (isRefinedBy_refl _) false false) false false)

/-! ### canonicalize_icmp :  (icmp pred C x) → (icmp (swapped pred) x C)

  `op` is the `icmp`; its lhs is a constant, rhs is not. The rewrite swaps the operands and maps the
  predicate. Source and target compute the *same* comparison (`icmp_swap`), so the value refinement
  follows by commuting operands/predicate then `icmp_mono`. Width-generic; `IcmpProperties` carries
  only the predicate so there is no poison-flag concern. -/

set_option maxHeartbeats 1000000 in
theorem canonicalizeIcmpLocal_preservesSemantics
    {h : LocalRewritePattern.ReturnOps canonicalizeIcmpLocal}
    {h₂ : LocalRewritePattern.ReturnCtxChanges canonicalizeIcmpLocal}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds canonicalizeIcmpLocal}
    {h₄ : LocalRewritePattern.ReturnValues canonicalizeIcmpLocal} :
    LocalRewritePattern.PreservesSemantics canonicalizeIcmpLocal h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, canonicalizeIcmpLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchIcmp`.
  have hMatchSome : (matchIcmp op ctx.raw).isSome := by
    cases hM : matchIcmp op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, ip⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchIcmp_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts: `i1` result, the two operands share a type.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, ⟨i1ty, hResType, hResBw⟩, hOperandTypesEq⟩ :=
    OperationPtr.Verified.llvm_icmp opVerif hOpType
  have hlhsEqOp : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hrhsEqOp : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hlhsEqOp]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hrhsEqOp]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  rw [hOperand0, hOperand1] at hOperandTypesEq
  -- Peel the lhs-constant guard.
  have hCstLhsSome : (matchConstantIntVal lhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal lhs ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨clhs, hCstLhs⟩ := Option.isSome_iff_exists.mp hCstLhsSome
  rw [hCstLhs] at hpattern
  simp only [] at hpattern
  -- Peel the rhs-not-constant guard.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hCstRhs
  -- Derive `lhs`'s integer type from its defining constant op.
  obtain ⟨cstPtr, hlhsPtr, hCstOp⟩ := matchConstantIntVal_implies hCstLhs
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hLhsIn : lhs.InBounds ctx.raw := by rw [← hOperand0]; grind
  have hOpResIn : (ValuePtr.opResult cstPtr).InBounds ctx.raw := hlhsPtr ▸ hLhsIn
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨lt, hCstResV⟩ :=
    OperationPtr.Verified.llvm_mlir__constant_resultType hCstVerified hCstType hCstProps
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType lt := by
    rw [hlhsPtr, ValuePtr.getType!_opResult, hCstEq]; exact hCstResV
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType lt := by
    rw [← hOperandTypesEq, hLhsType]
  -- Unfold the source `icmp`: result is `icmp lhsv rhsv ip.predicate`.
  obtain ⟨lhsv, rhsv, hlhsVal, hrhsVal, hMem, hRes, hCf⟩ :=
    matchIcmp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hinterp
      hLhsType hRhsType
  subst hCf
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Dominance / freshness for both operands.
  have hDomL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hRIn : rhs.InBounds ctx.raw := by rw [← hOperand1]; grind
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the single created `icmp` (operands `#[rhs, lhs]`), transporting `rhs`'s dominance.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomR hDomR₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm .icmp := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[rhs, lhs] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType i1ty,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) (Subtype.ext hResType)
  -- The created predicate is `ip.predicate` swapped.
  have hP : (newOp.getProperties! ctx₁.raw (.llvm .icmp)).predicate
      = (match ip.predicate with
          | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
          | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
          | q => q) := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hDomL₁ : lhs.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomL
  -- Read both refined operands in the target state.
  obtain ⟨rt, hRVal', hrRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRIn hrhsVal
      hDomR hDomR₁ rNotOp
  obtain ⟨ltv, hLVal', hlRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hlhsVal
      hDomL hDomL₁ lNotOp
  -- Replay the created `icmp` forward: operands `#[rhs, lhs]` give `icmp rt ltv (created pred)`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_icmp_forward (state := state') (inBounds := by grind)
      (it := lt) (i1t := i1ty)
      (props := newOp.getProperties! ctx₁.raw (.llvm .icmp))
      (f := fun a b => Data.LLVM.Int.icmp a b
        (newOp.getProperties! ctx₁.raw (.llvm .icmp)).predicate)
      hResBw
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hNewType rfl hNewOperands hNewResTypes hRVal' hLVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 1 (Data.LLVM.Int.icmp rt ltv
      (newOp.getProperties! ctx₁.raw (.llvm .icmp)).predicate)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- `icmp lhsv rhsv pred ⊒ icmp rt ltv (swapped pred)` by `icmp_swap` then `icmp_mono`.
  simp only [Data.LLVM.Int.cast_self]
  rw [hP, Data.LLVM.Int.icmp_swap lhsv rhsv ip.predicate]
  exact Data.LLVM.Int.icmp_mono rhsv lhsv rt ltv _ hrRef hlRef

/-! ### select_not :  select (not c) x y → select c y x

  `op` is the `select`; its condition operand is a defining `not` (`xor c (-1)`, recovered via
  `matchNot_getVar?_of_EquationLemmaAt`). The rewrite drops the `not` and swaps the two arms.
  Swapping the condition polarity is exactly cancelled by swapping the arms, so source and target
  are *equal* (`select_not_swap`); the value refinement then follows by `select_mono`. Width-generic
  over the (integer) arm width; the condition is `i1`. -/

set_option maxHeartbeats 1000000 in
theorem selectNotLocal_preservesSemantics
    {h : LocalRewritePattern.ReturnOps selectNotLocal}
    {h₂ : LocalRewritePattern.ReturnCtxChanges selectNotLocal}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds selectNotLocal}
    {h₄ : LocalRewritePattern.ReturnValues selectNotLocal} :
    LocalRewritePattern.PreservesSemantics selectNotLocal h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, selectNotLocal]
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
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts: `i1` condition, arms share the result type.
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
  -- Peel `matchNot cond`: `cond` is a defining `not`.
  have hNotSome : (matchNot cond ctx.raw).isSome := by
    cases hM : matchNot cond ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨c, hNot⟩ := Option.isSome_iff_exists.mp hNotSome
  rw [hNot] at hpattern
  simp only [] at hpattern
  -- Peel the result-type (arm) integer guard.
  obtain ⟨rt, hResType⟩ :
      ∃ rt, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType rt := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Operand types.
  have hCondType : (cond.getType! ctx.raw).val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := condIt; simp only at hCondBw; subst hCondBw; rw [← hOperand0, hCondTy]
  have hTvType : (tv.getType! ctx.raw).val = Attribute.integerType rt := by
    rw [← hOperand1, ← hResEqT, hResType]
  have hFvType : (fv.getType! ctx.raw).val = Attribute.integerType rt := by
    rw [← hOperand2, ← hResEqF, hResType]
  -- Unfold the matched `select`'s interpretation.
  obtain ⟨cv, tvv, fvv, hcondVal, htVal, hfVal, hMem, hRes, hCf⟩ :=
    matchSelectOp_interpretOp_unfold opInBounds hOpType hNumResults hOperands
      hCondType hTvType hFvType hinterp
  subst hCf
  -- Recover the `not`'s inner value `c` and `cond = xor c (-1)`.
  have hCondMem : cond ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨cvVal, hcVal, hCondNot, hcType, hDomC, hcIn, cNotOp⟩ :=
    matchNot_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hNot hCondMem hCondType
  obtain rfl : cv = Data.LLVM.Int.xor cvVal (Data.LLVM.Int.constant 1 (-1)) := by
    have := hcondVal.symm.trans hCondNot; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Dominance / freshness for the two arm operands.
  have hDomT : tv.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomF : fv.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hTIn : tv.InBounds ctx.raw := by rw [← hOperand1]; grind
  have hFIn : fv.InBounds ctx.raw := by rw [← hOperand2]; grind
  have tNotOp : ¬ tv ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have fNotOp : ¬ fv ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Peel the single created `select` (operands `#[c, fv, tv]`), transporting `c`'s dominance.
  peelOpCreation! hpattern ctx₁ newOp hNew hDomC hDomC₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .llvm .select := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[c, fv, tv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(⟨Attribute.integerType rt,
          hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) (Subtype.ext hResType)
  have hDomF₁ : fv.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomF
  have hDomT₁ : tv.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomT
  -- Read the three refined operands in the target state.
  obtain ⟨cvt, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hcIn hcVal
      hDomC hDomC₁ cNotOp
  obtain ⟨fvt, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFIn hfVal
      hDomF hDomF₁ fNotOp
  obtain ⟨tvt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTIn htVal
      hDomT hDomT₁ tNotOp
  -- Replay the created `select`: operands `#[c, fv, tv]` give `select cvt fvt tvt`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_llvm_select_forward (state := state') (inBounds := by grind)
      (it := rt) hNewType hNewOperands hNewResTypes hCVal' hFVal' hTVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int rt.bitwidth (Data.LLVM.Int.select cvt fvt tvt)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- `select (not cvVal) tvv fvv ⊒ select cvt fvt tvt` by `select_not_swap` then `select_mono`.
  simp only [Data.LLVM.Int.cast_self]
  rw [Data.LLVM.Int.select_not_swap cvVal tvv fvv]
  exact Data.LLVM.Int.select_mono fvv tvv fvt tvt cvVal cvt hfRef htRef hcRef

/-! ## RISC-V-dialect idempotent-extension folds (`riscv.<ext> (riscv.<ext> x) -> riscv.<ext> x`)

  These combines rewrite *already-selected* RISC-V ops. Because `Data.RISCV.Reg` is total (no
  poison), refinement on `RuntimeValue.reg` is plain equality, so the data-level obligation is the
  ordinary idempotence `f (f x) = f x` (already proven in `Veir/Passes/RISCVCombines/Proofs.lean`).
  The shared proof `drop_redundant_ext_local_preservesSemantics` is instantiated per width extension;
  the register-dialect scaffolding it relies on lives in `CommonBaseLemmas.lean`
  (`exists_refined_reg_getVar?`) and `CommonGraphLemmas.lean`
  (`matchRiscvUnaryReg_interpretOp_unfold`, `riscv_unaryReg_getVar?_of_EquationLemmaAt`, and the
  `OperationPtr.Pure.riscv_*` purity facts). -/

set_option maxHeartbeats 1000000 in
/-- Shared correctness for the idempotent-extension fold `riscv.<ext> (riscv.<ext> x) ->
    riscv.<ext> x`, over any unary reg-to-reg `riscv` op `ext` whose data-level action `f` is
    idempotent (`hIdem`). No ops are created; `op`'s result is forwarded to its operand `outerSrc`.
    The graph lemma shows `outerSrc` is `f w` for some register `w`, so the dropped outer result
    `f (f w) = f w = outerSrc` matches — an exact equality, since registers carry no poison. -/
theorem drop_redundant_ext_local_preservesSemantics {ext : Riscv}
    {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv ext → opp.Pure c)
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (f r)], mem, none))
    (hIdem : ∀ x, f (f x) = f x)
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local ext)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local ext)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local ext)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local ext)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local ext) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, drop_redundant_ext_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp`.
  have hMatchSome : (matchOp op ctx.raw (.riscv ext) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv ext) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, oProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp`.
  have hDefSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨innerOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  -- Peel the inner `matchOp`.
  have hInnerMatchSome : (matchOp innerOp ctx.raw (.riscv ext) 1).isSome := by
    cases hIM : matchOp innerOp ctx.raw (.riscv ext) 1 with
    | some y => rfl
    | none => rw [hIM] at hpattern; simp at hpattern
  obtain ⟨⟨iOperands, iProps⟩, hInnerMatch⟩ := Option.isSome_iff_exists.mp hInnerMatchSome
  rw [hInnerMatch] at hpattern
  simp only [] at hpattern
  -- Read off the pattern outputs: nothing is created, the result forwards to `operands[0]!`.
  obtain ⟨rfl, rfl, rfl⟩ : ctx = newCtx ∧ newOps = #[] ∧ newValues = #[operands[0]!] := by
    simp at hpattern; grind
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, -⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  -- Unfold the outer op's interpretation.
  obtain ⟨v, hOuterSrcVal, hMem, hResVal, hCf⟩ :=
    matchRiscvUnaryReg_interpretOp_unfold (rop := ext) (f := f) opInBounds hOpType hNumResults
      hOperands hSem hinterp
  subst hCf
  -- The forwarded operand dominates the match point and is not one of `op`'s results.
  have hDomOuter : (operands[0]!).dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hOuterNotOp : ¬ operands[0]! ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- The graph lemma pins the operand's value to `f w`, so the dropped `f` is idempotent on it.
  obtain ⟨w, hGraphVal⟩ :=
    riscv_unaryReg_getVar?_of_EquationLemmaAt (rop := ext) (f := f) ctxDom ctxVerif opInBounds
      stateWf hPure hSem hDef hInnerMatch (by simp [hOperands])
  obtain rfl : v = f w := by
    have := hOuterSrcVal.symm.trans hGraphVal; simpa using this
  -- `sourceValues` is the single dropped result value `.reg (f (f w))`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Read the forwarded operand's value in the target state (register refinement is equality).
  have hOuterTgt :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom (by grind)
      hOuterSrcVal hDomOuter hDomOuter hOuterNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.reg (f w)], by simp [hOuterTgt, Option.bind, Option.map], ?_⟩
  exact RuntimeValue.arrayIsRefinedBy_singleton.mpr (hIdem w)

theorem sexth_sexth_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .sexth)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .sexth)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .sexth)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .sexth)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .sexth) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.sexth)
    (fun hType => OperationPtr.Pure.riscv_sexth hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.sexth_sexth (x := x))

theorem sextb_sextb_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .sextb)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .sextb)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .sextb)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .sextb)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .sextb) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.sextb)
    (fun hType => OperationPtr.Pure.riscv_sextb hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.sextb_sextb (x := x))

theorem zexth_zexth_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .zexth)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .zexth)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .zexth)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .zexth)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .zexth) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.zexth)
    (fun hType => OperationPtr.Pure.riscv_zexth hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.zexth_zexth (x := x))

theorem zextb_zextb_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .zextb)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .zextb)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .zextb)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .zextb)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .zextb) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.zextb)
    (fun hType => OperationPtr.Pure.riscv_zextb hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.zextb_zextb (x := x))

theorem sextw_sextw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .sextw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .sextw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .sextw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .sextw)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .sextw) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.sextw)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.sextw_sextw (x := x))

theorem zextw_zextw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_redundant_ext_local .zextw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_redundant_ext_local .zextw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_redundant_ext_local .zextw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_redundant_ext_local .zextw)} :
    LocalRewritePattern.PreservesSemantics (drop_redundant_ext_local .zextw) h h₂ h₃ h₄ :=
  drop_redundant_ext_local_preservesSemantics
    (f := Data.RISCV.zextw)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun x => Veir.Data.RISCV.zextw_zextw (x := x))

/-! ### combine_or_of_and :  `or (and x, y), x → x`

  `op` is the `or`; one of its operands is the kept value `x`, the other is a defining `and` one of
  whose operands is that same `x`. No operation is created: the `or`'s result is replaced by `x`.
  The defining `and`'s value is recovered with `matchBinop_getVar?_of_EquationLemmaAt`, and the
  obligation collapses to the width-generic absorption lemmas `OrAndAbsorbL`/`OrAndAbsorbR` (the
  `and`'s matched operand may be on either side, normalised with `and_comm`). The `or`'s `disjoint`
  flag stays a free variable -- a `disjoint` `or` that overlaps is merely poison, and `poison ⊒ x`.
-/

set_option maxHeartbeats 1000000 in
/-- Shared correctness proof for `combine_or_of_and_l` (`andOnLeft := true`) and
    `combine_or_of_and_r` (`andOnLeft := false`). -/
theorem orOfAndLocal_preservesSemantics (andOnLeft : Bool)
    {h : LocalRewritePattern.ReturnOps (orOfAndLocal andOnLeft)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (orOfAndLocal andOnLeft)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (orOfAndLocal andOnLeft)}
    {h₄ : LocalRewritePattern.ReturnValues (orOfAndLocal andOnLeft)} :
    LocalRewritePattern.PreservesSemantics (orOfAndLocal andOnLeft) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, orOfAndLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchOr`.
  have hMatchSome : (matchOr op ctx.raw).isSome := by
    cases hM : matchOr op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨m0, m1, oprops⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, -⟩ := matchOr_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Verifier facts for `op` (the `or`).
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_or opVerif hOpType
  have hOperand0 : op.getOperand! ctx.raw 0 = m0 := by
    rw [show m0 = (op.getOperands! ctx.raw)[0]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = m1 := by
    rw [show m1 = (op.getOperands! ctx.raw)[1]! from by rw [hOperands]; rfl]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hM0Type : (m0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hM1Type : (m1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer `or`'s interpretation: source value is `or m0v m1v disjoint`.
  obtain ⟨m0v, m1v, hM0Val, hM1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .or)
      (srcFn := fun a b props => Data.LLVM.Int.or a b props.disjoint)
      (props := op.getProperties! ctx.raw (.llvm .or))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hM0Type hM1Type
  subst hCf
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Split on which side of the `or` carries the `and`.
  cases andOnLeft with
  | true =>
    simp only [reduceIte] at hpattern
    -- `andV = m0`, `x = m1`.
    have hDefSome : (getDefiningOp m0 ctx.raw).isSome := by
      cases hM : getDefiningOp m0 ctx.raw with
      | some z => rfl
      | none => rw [hM] at hpattern; simp at hpattern
    obtain ⟨andOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
    rw [hDef] at hpattern
    simp only [] at hpattern
    have hAndSome : (matchAnd andOp ctx.raw).isSome := by
      cases hM : matchAnd andOp ctx.raw with
      | some z => rfl
      | none => rw [hM] at hpattern; simp at hpattern
    obtain ⟨⟨a0, a1, andP⟩, hAnd⟩ := Option.isSome_iff_exists.mp hAndSome
    rw [hAnd] at hpattern
    simp only [] at hpattern
    split at hpattern
    case isTrue => simp at hpattern
    rename_i hGuard
    have hax : a0 = m1 ∨ a1 = m1 := by
      simp only [not_and, Decidable.not_not] at hGuard
      rcases Decidable.em (a0 = m1) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (hGuard hh)
    obtain ⟨a0v, a1v, ha0Val, ha1Val, hAndValIs, -, -, ha0Dom, ha1Dom, ha0In, ha1In,
        ha0NotOp, ha1NotOp⟩ :=
      matchBinop_getVar?_of_EquationLemmaAt (srcOp := .and)
        (srcFn := fun a b _ => Data.LLVM.Int.and a b)
        (matchBinopNoProps_implies matchAnd_implies)
        OperationPtr.Verified.llvm_and OperationPtr.Pure.llvm_and
        (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
        ctxDom ctxVerif opInBounds stateWf hDef
        (show matchBinopNoProps matchAnd andOp ctx.raw = some (a0, a1) by
          simp only [matchBinopNoProps, bind, Option.bind, hAnd])
        (by rw [hOperands]; simp) hM0Type
    -- `m1` is the kept operand and equals `a0` or `a1`, so it inherits their source facts.
    have hDomKeep : m1.dominatesIp (InsertPoint.before op) ctx := by
      rcases hax with h | h
      · exact h ▸ ha0Dom
      · exact h ▸ ha1Dom
    have hKeepIn : m1.InBounds ctx.raw := by
      rcases hax with h | h
      · exact h ▸ ha0In
      · exact h ▸ ha1In
    have keepNotOp : ¬ m1 ∈ op.getResults! ctx.raw := by
      rcases hax with h | h
      · exact h ▸ ha0NotOp
      · exact h ▸ ha1NotOp
    obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[m1] := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hpattern; grind
    obtain ⟨kt, hKeepVal', hktRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hKeepIn hM1Val
        hDomKeep hDomKeep keepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by simp [hKeepVal', Option.bind, Option.map],
      ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    refine isRefinedBy_trans ?_ hktRef
    -- Data: `or m0v m1v disjoint ⊒ m1v`, with `m0v = and a0v a1v` and `a0 = m1 ∨ a1 = m1`.
    have hm0v : m0v = Data.LLVM.Int.and a0v a1v := by
      have := hM0Val.symm.trans hAndValIs; simpa using this
    subst hm0v
    simp only [Data.LLVM.Int.cast_self]
    rcases hax with ha | ha
    · have hEq : a0v = m1v := by
        have := (ha ▸ ha0Val).symm.trans hM1Val; simpa using this
      subst hEq
      exact Data.LLVM.Int.OrAndAbsorbL
    · have hEq : a1v = m1v := by
        have := (ha ▸ ha1Val).symm.trans hM1Val; simpa using this
      subst hEq
      rw [Data.LLVM.Int.and_comm]
      exact Data.LLVM.Int.OrAndAbsorbL
  | false =>
    simp only [Bool.false_eq_true, reduceIte] at hpattern
    -- `andV = m1`, `x = m0`.
    have hDefSome : (getDefiningOp m1 ctx.raw).isSome := by
      cases hM : getDefiningOp m1 ctx.raw with
      | some z => rfl
      | none => rw [hM] at hpattern; simp at hpattern
    obtain ⟨andOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
    rw [hDef] at hpattern
    simp only [] at hpattern
    have hAndSome : (matchAnd andOp ctx.raw).isSome := by
      cases hM : matchAnd andOp ctx.raw with
      | some z => rfl
      | none => rw [hM] at hpattern; simp at hpattern
    obtain ⟨⟨a0, a1, andP⟩, hAnd⟩ := Option.isSome_iff_exists.mp hAndSome
    rw [hAnd] at hpattern
    simp only [] at hpattern
    split at hpattern
    case isTrue => simp at hpattern
    rename_i hGuard
    have hax : a0 = m0 ∨ a1 = m0 := by
      simp only [not_and, Decidable.not_not] at hGuard
      rcases Decidable.em (a0 = m0) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (hGuard hh)
    obtain ⟨a0v, a1v, ha0Val, ha1Val, hAndValIs, -, -, ha0Dom, ha1Dom, ha0In, ha1In,
        ha0NotOp, ha1NotOp⟩ :=
      matchBinop_getVar?_of_EquationLemmaAt (srcOp := .and)
        (srcFn := fun a b _ => Data.LLVM.Int.and a b)
        (matchBinopNoProps_implies matchAnd_implies)
        OperationPtr.Verified.llvm_and OperationPtr.Pure.llvm_and
        (fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
        ctxDom ctxVerif opInBounds stateWf hDef
        (show matchBinopNoProps matchAnd andOp ctx.raw = some (a0, a1) by
          simp only [matchBinopNoProps, bind, Option.bind, hAnd])
        (by rw [hOperands]; simp) hM1Type
    -- `m0` is the kept operand and equals `a0` or `a1`, so it inherits their source facts.
    have hDomKeep : m0.dominatesIp (InsertPoint.before op) ctx := by
      rcases hax with h | h
      · exact h ▸ ha0Dom
      · exact h ▸ ha1Dom
    have hKeepIn : m0.InBounds ctx.raw := by
      rcases hax with h | h
      · exact h ▸ ha0In
      · exact h ▸ ha1In
    have keepNotOp : ¬ m0 ∈ op.getResults! ctx.raw := by
      rcases hax with h | h
      · exact h ▸ ha0NotOp
      · exact h ▸ ha1NotOp
    obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[m0] := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hpattern; grind
    obtain ⟨kt, hKeepVal', hktRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hKeepIn hM0Val
        hDomKeep hDomKeep keepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by simp [hKeepVal', Option.bind, Option.map],
      ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    refine isRefinedBy_trans ?_ hktRef
    -- Data: `or m0v m1v disjoint ⊒ m0v`, with `m1v = and a0v a1v` and `a0 = m0 ∨ a1 = m0`.
    have hm1v : m1v = Data.LLVM.Int.and a0v a1v := by
      have := hM1Val.symm.trans hAndValIs; simpa using this
    subst hm1v
    simp only [Data.LLVM.Int.cast_self]
    rcases hax with ha | ha
    · have hEq : a0v = m0v := by
        have := (ha ▸ ha0Val).symm.trans hM0Val; simpa using this
      subst hEq
      exact Data.LLVM.Int.OrAndAbsorbR
    · have hEq : a1v = m0v := by
        have := (ha ▸ ha1Val).symm.trans hM0Val; simpa using this
      subst hEq
      rw [Data.LLVM.Int.and_comm]
      exact Data.LLVM.Int.OrAndAbsorbR

theorem combine_or_of_and_l_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (orOfAndLocal true)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (orOfAndLocal true)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (orOfAndLocal true)}
    {h₄ : LocalRewritePattern.ReturnValues (orOfAndLocal true)} :
    LocalRewritePattern.PreservesSemantics (orOfAndLocal true) h h₂ h₃ h₄ :=
  orOfAndLocal_preservesSemantics true

theorem combine_or_of_and_r_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (orOfAndLocal false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (orOfAndLocal false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (orOfAndLocal false)}
    {h₄ : LocalRewritePattern.ReturnValues (orOfAndLocal false)} :
    LocalRewritePattern.PreservesSemantics (orOfAndLocal false) h h₂ h₃ h₄ :=
  orOfAndLocal_preservesSemantics false

/-! ### right_identity_zero_add :  riscv.add x (riscv.li 0) → x

  The first combine to match *RISC-V-dialect* ops as source. RISC-V register values are total (no
  poison), so `.reg r ⊒ .reg r'` is plain equality and the obligation collapses to the register
  identity `RISCV.add (li 0) x = x` (`Data.RISCV.right_identity_zero_add_comm` in `Proofs.lean` —
  the interpreter computes `RISCV.add op2 op1`, so the materialized `li 0` lands as the *first*
  argument). The scaffolding below (a `riscv.li` purity fact, `.riscv .add`/`.li` interpretation
  unfolders that read the register operands straight off the interpreter's own `[.reg, .reg]`
  pattern-match — the verifier does not pin register-typedness — and a register value-refinement
  reader) parallels the LLVM Layer-1/Layer-3 pieces used by the constant combines. -/

/-- `riscv.li` is pure: its interpretation neither reads nor writes memory. -/
private theorem riscv_li_pure {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .riscv .li) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Riscv.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- Interpreting a `riscv.li` binds its result to `RISCV.li` of its immediate (a non-poison
    register). Applied at `newState := state` this unfolds the `EquationHolds` fact of a matched
    defining `li`. The register analogue of `constantOp_interpretOp_unfold`; note the `li`
    interpreter ignores the result type, so no result-type hypothesis is needed. -/
private theorem riscvLiOp_interpretOp_unfold {ctx : WfIRContext OpCode} {liOp : OperationPtr}
    {state newState : InterpreterState ctx} {cf} (inBounds : liOp.InBounds ctx.raw)
    (hOpType : liOp.getOpType! ctx.raw = .riscv .li)
    (hNumResults : liOp.getNumResults! ctx.raw = 1)
    (hinterp : interpretOp liOp state inBounds = some (.ok (newState, cf))) :
    newState.variables.getVar? (liOp.getResult 0) =
      some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64
        (liOp.getProperties! ctx.raw (.riscv .li)).value.value))) := by
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Riscv.interpretOp', pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64
        (liOp.getProperties! ctx.raw (.riscv .li)).value.value))] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Interpreting a matched `riscv.add` (whose right operand `rhs` is already known to be the
    register `r₂`) reads its left *register* operand value `r₁` — the interpreter returns `none`
    unless both operands are `.reg`, so `lhs`'s register-typedness is recovered from the interpreter's
    own pattern-match rather than from the verifier — and binds its result to `RISCV.add r₂ r₁`
    (the interpreter applies the operands reversed). The register analogue of
    `matchBinaryOp_interpretOp_unfold`. -/
private theorem riscvAddOp_interpretOp_unfold {ctx : WfIRContext OpCode} {op : OperationPtr}
    {lhs rhs : ValuePtr} {r₂ : Data.RISCV.Reg}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .riscv .add)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hNumOperands : op.getNumOperands! ctx.raw = 2)
    (hOperand0 : op.getOperand! ctx.raw 0 = lhs)
    (hOperand1 : op.getOperand! ctx.raw 1 = rhs)
    (hRhsVal : state.variables.getVar? rhs = some (RuntimeValue.reg r₂))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ r₁, state.variables.getVar? lhs = some (RuntimeValue.reg r₁) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.reg (Data.RISCV.add r₂ r₁)) ∧
      cf = none := by
  obtain ⟨operandValues, _, _, _, hOV, _⟩ := interpretOp_some_iff.mp hinterp
  have ⟨hsz, hvals⟩ := VariableState.getOperandValues_eq_some_iff.mp hOV
  rw [hNumOperands] at hsz hvals
  have hlval := hvals 0 (by omega); rw [hOperand0] at hlval
  have hOpVals : state.variables.getOperandValues op
      = some #[operandValues[0]!, RuntimeValue.reg r₂] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by rw [hNumOperands]; simp, fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => rw [hOperand0]; simpa using hlval
    | 1, _ => rw [hOperand1, hRhsVal]; simp
  rw [interpretOp_ok_iff_of_getOperandValues_eq_some hOpVals] at hinterp
  obtain ⟨resValues, hInterp', hSet⟩ := hinterp
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp'] at hInterp'
  -- The interpreter's `[.reg op1, .reg op2]` match forces `lhs` to be a register.
  cases hlv : operandValues[0]! with
  | reg r₁ =>
    rw [hlv] at hInterp'
    simp only [Riscv.interpretOp', pure, Interp] at hInterp'
    obtain ⟨rfl, hmem, rfl⟩ :
        resValues = #[RuntimeValue.reg (Data.RISCV.add r₂ r₁)] ∧
        newState.memory = state.memory ∧ cf = none := by grind
    refine ⟨r₁, ?_, hmem.symm, ?_, rfl⟩
    · rw [hlval, hlv]
    · rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
      simp
  | int _ _ => rw [hlv] at hInterp'; simp [Riscv.interpretOp'] at hInterp'
  | byte _ _ => rw [hlv] at hInterp'; simp [Riscv.interpretOp'] at hInterp'
  | addr _ => rw [hlv] at hInterp'; simp [Riscv.interpretOp'] at hInterp'
  | float _ _ => rw [hlv] at hInterp'; simp [Riscv.interpretOp'] at hInterp'

-- The register analogue of `exists_refined_int_getVar?` lives in `CommonBaseLemmas.lean` as
-- `LocalRewritePattern.exists_refined_reg_getVar?`, beside the int and byte readers.

set_option maxHeartbeats 1000000 in
theorem right_identity_zero_add_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps right_identity_zero_add_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges right_identity_zero_add_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds right_identity_zero_add_local}
    {h₄ : LocalRewritePattern.ReturnValues right_identity_zero_add_local} :
    LocalRewritePattern.PreservesSemantics right_identity_zero_add_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, right_identity_zero_add_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchOp op (.riscv .add) 2`.
  have hMatchSome : (matchOp op ctx.raw (.riscv .add) 2).isSome := by
    cases hM : matchOp op ctx.raw (.riscv .add) 2 with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, addProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, -⟩ := matchOp_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp operands[1]!`.
  have hDefSome : (getDefiningOp operands[1]! ctx.raw).isSome := by
    cases hM : getDefiningOp operands[1]! ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨liOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  -- Peel `matchOp liOp (.riscv .li) 0`.
  have hLiSome : (matchOp liOp ctx.raw (.riscv .li) 0).isSome := by
    cases hM : matchOp liOp ctx.raw (.riscv .li) 0 with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨liOperands, cst⟩, hLiMatch⟩ := Option.isSome_iff_exists.mp hLiSome
  obtain ⟨hLiType, -, hLiNumResults, -, hLiProps⟩ := matchOp_implies hLiMatch
  rw [hLiMatch] at hpattern
  simp only [] at hpattern
  -- The `cst.value.value = 0` guard (the initial `simp` swapped the negated `if`).
  have hCst0 : cst.value.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCst0] at hpattern
  -- Structural facts. Recover the two-operand pair form.
  have hOperandsArr : op.getOperands! ctx.raw = operands := hOperandsEq.symm
  have hOpSz : operands.size = 2 := by
    rw [← hOperandsArr, OperationPtr.getOperands!.size_eq_getNumOperands!]; exact hNumOperands
  have hOperandsPair : op.getOperands! ctx.raw = #[operands[0]!, operands[1]!] := by
    rw [hOperandsArr]
    rcases operands with ⟨l⟩
    rw [List.size_toArray] at hOpSz
    match l, hOpSz with
    | [a, b], _ => rfl
  have hLhsEq : operands[0]! = (op.getOperands! ctx.raw)[0]! := by rw [hOperandsPair]; simp
  have hRhsEq : operands[1]! = (op.getOperands! ctx.raw)[1]! := by rw [hOperandsPair]; simp
  have hOperand0 : op.getOperand! ctx.raw 0 = operands[0]! := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = operands[1]! := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hRhsMem : operands[1]! ∈ op.getOperands! ctx.raw := by rw [hOperandsPair]; simp
  have hLhsMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperandsPair]; simp
  -- `operands[1]!` is a result of `liOp`, hence dominates `op`.
  obtain ⟨liPtr, hRhsPtr, hLiOpEq⟩ :
      ∃ p, operands[1]! = ValuePtr.opResult p ∧ p.op = liOp := by
    match hm : operands[1]! with
    | .opResult p => exact ⟨p, rfl, by rw [hm] at hDef; simpa [getDefiningOp] using hDef⟩
    | .blockArgument p => rw [hm] at hDef; simp [getDefiningOp] at hDef
  subst hLiOpEq
  have hRhsIn : operands[1]!.InBounds ctx.raw := by grind
  have hLiOpIn : liPtr.op.InBounds ctx.raw := by
    rw [hRhsPtr] at hRhsIn; grind [OpResultPtr.InBounds]
  have hLiIdx : liPtr.index < liPtr.op.getNumResults! ctx.raw := by
    rw [hRhsPtr] at hRhsIn
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!, OpResultPtr.InBounds]
  have hLiEq : liPtr = liPtr.op.getResult 0 := by
    have hidx : liPtr.index = 0 := by omega
    cases liPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hLiDefines : (ValuePtr.opResult liPtr).getDefiningOp! ctx.raw = some liPtr.op := by
    have hOwner := (ctx.wellFormed.operations liPtr.op hLiOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hLiSDom : liPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hLiDefines (by rw [← hRhsPtr]; exact hRhsMem)
  have hLiDomIp : liPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hLiPure : liPtr.op.Pure ctx.raw := riscv_li_pure hLiType
  obtain ⟨cfLi, hInterpLi⟩ := stateWf liPtr.op hLiOpIn hLiPure hLiDomIp
  -- The `li`'s runtime value: `RISCV.li 0`.
  have hLiVal := riscvLiOp_interpretOp_unfold hLiOpIn hLiType hLiNumResults hInterpLi
  have hCstVal0 : (liPtr.op.getProperties! ctx.raw (.riscv .li)).value.value = 0 := by
    rw [hLiProps] at hCst0; exact hCst0
  rw [hCstVal0] at hLiVal
  have hRhsVal : state.variables.getVar? operands[1]!
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 0))) := by
    rw [hRhsPtr, hLiEq]; exact hLiVal
  -- Unfold the `add`'s interpretation (its right operand is `li 0`).
  obtain ⟨r₁, hLhsVal, hMem, hRes, hCf⟩ :=
    riscvAddOp_interpretOp_unfold opInBounds hOpType hNumResults hNumOperands
      hOperand0 hOperand1 hRhsVal hinterp
  subst hCf
  -- `operands[0]!` dominance / freshness facts (a direct operand of `op`).
  have hDomLhs : operands[0]!.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have lhsNotOp : ¬ operands[0]! ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have hLhsIn : operands[0]!.InBounds ctx.raw := by grind
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Nothing is created: `newCtx = ctx`, `newOps = #[]`, `newValues = #[operands[0]!]`.
  obtain ⟨rfl, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[operands[0]!] := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hpattern; grind
  have hLhsVal' := LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hLhsIn hLhsVal
    hDomLhs hDomLhs lhsNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.reg r₁], by simp [hLhsVal', Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  -- `.reg (RISCV.add (li 0) r₁) ⊒ .reg r₁`  ⟺  `RISCV.add (li 0) r₁ = r₁`.
  simp only [RuntimeValue.isRefinedBy]
  exact Data.RISCV.right_identity_zero_add_comm

/-! ### sub_to_add :  sub x C → add x (-C)   (C constant)

  Matches `sub x C` where `C` is a matched integer constant (a *direct* operand — no defining op is
  inspected), then creates a fresh `llvm.mlir.constant` holding `-C` and one `add x (-C)` whose
  overflow flags are *cleared* (see the flag-threading note in `LLVMProofs.lean`). Simpler than the
  constant-reassociation family: the left operand `x` is read directly off the outer `sub`, so no
  `matchBinop*Const_getVar?` graph lemma is needed. Unfold the `sub`'s interpretation with
  `matchBinaryOp_interpretOp_unfold`, pin its constant operand with `matchConstantIntVal_getVar?…`,
  replay the created constant (`interpretOp_llvm_constant_forward`) and `add`
  (`interpretOp_llvm_binaryInt_forward`), and close with `Data.LLVM.Int.SubToAddNeg`. -/

set_option maxHeartbeats 1000000 in
theorem sub_to_add_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps sub_to_add_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges sub_to_add_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds sub_to_add_local}
    {h₄ : LocalRewritePattern.ReturnValues sub_to_add_local} :
    LocalRewritePattern.PreservesSemantics sub_to_add_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, sub_to_add_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchSub op`: operands `#[x, cval]`.
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨x, cval, sProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hSubType, hSubNumResults, hSubOperands, -⟩ := matchSub_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel the constant operand `cval`.
  have hCSome : (matchConstantIntVal cval ctx.raw).isSome := by
    cases hM : matchConstantIntVal cval ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cAttr, hC⟩ := Option.isSome_iff_exists.mp hCSome
  rw [hC] at hpattern
  simp only [] at hpattern
  -- Verifier facts for the `sub`: operands/result share type `subType`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, subType, hSubResType, hSubOperand0Type, hSubOperand1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hSubType
  have hxEq : x = (op.getOperands! ctx.raw)[0]! := by rw [hSubOperands]; rfl
  have hCvalEq : cval = (op.getOperands! ctx.raw)[1]! := by rw [hSubOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = x := by
    rw [hxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = cval := by
    rw [hCvalEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand0, hSubOperand0Type]
  have hCvalType : (cval.getType! ctx.raw).val = Attribute.integerType subType := by
    rw [← hOperand1, hSubOperand1Type]
  -- Unfold the `sub`'s interpretation: `x`'s value and the constant operand's value.
  obtain ⟨xVal, cvalVal, hxVal, hCvalVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun a b p => Data.LLVM.Int.sub a b p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hSubType hSubNumResults hSubOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hxType hCvalType
  subst hCf
  -- Pin the constant operand's value.
  have hCvalConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hC (by rw [hSubOperands]; simp) hCvalType
  obtain rfl : cvalVal = Data.LLVM.Int.constant subType.bitwidth cAttr.value := by
    have := hCvalVal.symm.trans hCvalConst; simpa using this
  -- `x`'s dominance / freshness facts (a direct operand of `op`).
  have hDomX : x.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have xNotOp : ¬ x ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have hxIn : x.InBounds ctx.raw := by grind
  -- Width guard on `x`'s type.
  rw [hxType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  have hWidth : subType.bitwidth = 64 ∨ subType.bitwidth = 32 := by omega
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the two creations: the negated constant, then the `add`.
  peelOpCreation! hpattern ctx₁ cnOp hCn hDomX hDomX₁
  peelOpCreation! hpattern ctx₂ addNewOp hAddNew hDomX₁ hDomX₂
  cleanupHpattern hpattern
  have hCnNeAdd : cnOp ≠ addNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- `x`'s type as a `TypeAttr`, transported to `ctx₁`.
  have hxTypeAttr : x.getType! ctx.raw
      = (⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hxType
  have hxTypeAttr₁ : x.getType! ctx₁.raw
      = (⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hCn hxIn]; exact hxTypeAttr
  -- Structural facts for the negated constant.
  have hCnType : cnOp.getOpType! ctx₂.raw = .llvm .mlir__constant := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCn (operation := cnOp),
      OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := cnOp)]
  have hCnOperands : cnOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCn (operation := cnOp),
      OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := cnOp)]
  have hCnProps : (cnOp.getProperties! ctx₂.raw (.llvm .mlir__constant)).value
      = .integer ⟨-cAttr.value, subType⟩ := by
    have h1 := OperationPtr.getProperties!_WfRewriter_createOp hCn (operation := cnOp)
      (opType := OpCode.llvm Llvm.mlir__constant)
    rw [if_pos rfl] at h1
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hAddNew hCnNeAdd, h1]
  have hCnResTypes : cnOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCn (operation := cnOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := cnOp)
    rw [if_neg hCnNeAdd] at hT2
    rw [hT2, hT]
    exact congrArg (fun t => #[t]) hxTypeAttr
  -- Structural facts for the new `add`.
  have hAddNewType : addNewOp.getOpType! ctx₂.raw = .llvm .add := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewOperands : addNewOp.getOperands! ctx₂.raw = #[x, ValuePtr.opResult (cnOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewProps : addNewOp.getProperties! ctx₂.raw (.llvm .add) = { nsw := false, nuw := false } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hAddNew (operation := addNewOp)]
  have hAddNewResTypes : addNewOp.getResultTypes! ctx₂.raw
      = #[(⟨Attribute.integerType subType, hxType ▸ (x.getType! ctx.raw).2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hAddNew (operation := addNewOp)
    rw [if_pos rfl] at hT
    rw [hT]
    exact congrArg (fun t => #[t]) hxTypeAttr₁
  -- Read the refined `x` in the target state.
  obtain ⟨xt, hxVal', hxRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hxIn hxVal
      hDomX hDomX₂ xNotOp
  -- Replay the negated constant, then the `add`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_constant_forward (state := state') (inBounds := by grind)
      hCnType hCnProps hCnOperands hCnResTypes
  have hxVal₁ : s₁.variables.getVar? x = some (RuntimeValue.int subType.bitwidth xt) := by
    rw [hFrame₁ x (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hxIn
      (WfRewriter.createOp_new_not_inBounds cnOp hCn))]
    exact hxVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_llvm_binaryInt_forward (state := s₁) (inBounds := by grind)
      (f := fun a b => Data.LLVM.Int.add a b false false)
      (by intro resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp])
      hAddNewType hAddNewProps hAddNewOperands hAddNewResTypes hxVal₁ hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int subType.bitwidth
      (Data.LLVM.Int.add xt (Data.LLVM.Int.constant subType.bitwidth
        (-cAttr.value)) false false)],
    by simp [hRes₂, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `sub x (const C) .. ⊒ add x (const -C) .. ⊒ add xt (const -C) ..`.
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (Data.LLVM.Int.SubToAddNeg hWidth)
    (Data.LLVM.Int.add_mono _ _ _ _ hxRef (isRefinedBy_refl _) false false)

/-! ### funnel_shift_or_shift_to_funnel_shift

  `(fshl x z y) | (shl x y) → fshl x z y` and the mirror `(fshr z x y) | (lshr x y) → fshr z x y`.
  A pure value-replacement: `op` is the commutative `or`, whose two operands are recovered through
  their defining ops — one a ternary funnel shift (`matchFshl`/`matchFshr`, via the new ternary graph
  lemma `matchTernaryOp_getVar?_of_EquationLemmaAt`), one a plain shift (`matchShl`/`matchLshr`, via
  the existing `matchShl_getVar?_of_EquationLemmaAt` / its `lshr` analogue). The shift's set bits are
  a subset of the funnel shift's, so the `or` collapses to the funnel shift value that is kept. Both
  operand orders of the `or` are handled by the `.orElse` in the pattern; each is peeled and closed
  by the corresponding (direct/commuted) data lemma. -/

/-- Ternary analogue of `matchBinop_getVar?_of_EquationLemmaAt`: for an operand `base` of `op`
    defined by a three-operand integer op (`fshl`/`fshr`), recover its three operand values and the
    fact that `base`'s runtime value is `srcFn av bv cv`. -/
private theorem matchTernaryOp_getVar?_of_EquationLemmaAt {srcOp : Llvm}
    {srcFn : ∀ {bw : Nat}, Data.LLVM.Int bw → Data.LLVM.Int bw → Data.LLVM.Int bw →
      Data.LLVM.Int bw}
    {match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr)}
    (hMatchImplies : ∀ {opp : OperationPtr} {c : IRContext OpCode} {a b amt},
        match? opp c = some (a, b, amt) →
        opp.getOpType! c = .llvm srcOp ∧ opp.getNumResults! c = 1 ∧
          opp.getOperands! c = #[a, b, amt])
    (hVerified : ∀ {c : WfIRContext OpCode} {opp : OperationPtr} {oib : opp.InBounds c.raw},
        opp.Verified c oib → opp.getOpType! c.raw = .llvm srcOp → opp.IsVerifiedIntegerTernop c)
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .llvm srcOp → opp.Pure c)
    (hSemSrc : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props rt #[.int bw x, .int bw y, .int bw z] bo mem
          = some (.ok (#[.int bw (srcFn x y z)], mem, none)))
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {base a b amt : ValuePtr} {ternOp : OperationPtr} {intType : IntegerType}
    (hDef : getDefiningOp base ctx.raw = some ternOp)
    (hMatch : match? ternOp ctx.raw = some (a, b, amt))
    (hOperand : base ∈ op.getOperands! ctx.raw)
    (hBaseType : (base.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ av bv cv : Data.LLVM.Int intType.bitwidth,
      state.variables.getVar? a = some (RuntimeValue.int intType.bitwidth av) ∧
      state.variables.getVar? b = some (RuntimeValue.int intType.bitwidth bv) ∧
      state.variables.getVar? amt = some (RuntimeValue.int intType.bitwidth cv) ∧
      state.variables.getVar? base
        = some (RuntimeValue.int intType.bitwidth (srcFn av bv cv)) := by
  obtain ⟨hTernType, hTernNumResults, hTernOperands⟩ := hMatchImplies hMatch
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hTernOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hTernVerified : basePtr.op.Verified ctx hTernOpIn := by grind
  obtain ⟨-, -, -, -, ternIntType, hTernResType, hTernOp0Type, hTernOp1Type, hTernOp2Type⟩ :=
    hVerified hTernVerified hTernType
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  have hIntTypeEq : intType = ternIntType := by
    rw [hBaseTypeEq, hTernResType] at hBaseType; grind
  subst hIntTypeEq
  have haIdxEq : a = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hTernOperands]; rfl
  have hbIdxEq : b = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hTernOperands]; rfl
  have hamtIdxEq : amt = (basePtr.op.getOperands! ctx.raw)[2]! := by rw [hTernOperands]; rfl
  have hTernOperand0 : basePtr.op.getOperand! ctx.raw 0 = a := by
    rw [haIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hTernOperand1 : basePtr.op.getOperand! ctx.raw 1 = b := by
    rw [hbIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hTernOperand2 : basePtr.op.getOperand! ctx.raw 2 = amt := by
    rw [hamtIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have haType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hTernOperand0, hTernOp0Type]
  have hbType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hTernOperand1, hTernOp1Type]
  have hamtType : (amt.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hTernOperand2, hTernOp2Type]
  have hTernDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hTernOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hTernSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hTernDefines hOperand
  have hTernDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hTernPure : basePtr.op.Pure ctx.raw := hPure hTernType
  obtain ⟨cfT, hInterpTern⟩ := stateWf basePtr.op hTernOpIn hTernPure hTernDomIp
  obtain ⟨av, bv, cv, haVal, hbVal, hcVal, -, hTernResVal, -⟩ :=
    matchTernaryOp_interpretOp_unfold (srcFn := srcFn)
      hTernOpIn hTernType hTernNumResults hTernOperands hSemSrc
      hInterpTern haType hbType hamtType
  exact ⟨av, bv, cv, haVal, hbVal, hcVal, hBaseEq ▸ hTernResVal⟩

/-- Syntactic decomposition of a successful `funnelOrShlTryOrder`. -/
private theorem funnelOrShlTryOrder_some {ctx : WfIRContext OpCode} {fshlV shlV keep : ValuePtr}
    (h : funnelOrShlTryOrder ctx fshlV shlV = some keep) :
    keep = fshlV ∧ ∃ dFshl fx fz fy dShl sx sy shProps,
      getDefiningOp fshlV ctx = some dFshl ∧ matchFshl dFshl ctx = some (fx, fz, fy) ∧
      getDefiningOp shlV ctx = some dShl ∧ matchShl dShl ctx = some (sx, sy, shProps) ∧
      fx = sx ∧ fy = sy := by
  rw [funnelOrShlTryOrder] at h
  cases hDFshl : getDefiningOp fshlV ctx.raw with
  | none => simp [hDFshl] at h
  | some dFshl =>
    cases hFshl : matchFshl dFshl ctx.raw with
    | none => simp [hDFshl, hFshl] at h
    | some triple =>
      obtain ⟨fx, fz, fy⟩ := triple
      cases hDShl : getDefiningOp shlV ctx.raw with
      | none => simp [hDFshl, hFshl, hDShl] at h
      | some dShl =>
        cases hShl : matchShl dShl ctx.raw with
        | none => simp [hDFshl, hFshl, hDShl, hShl] at h
        | some striple =>
          obtain ⟨sx, sy, shProps⟩ := striple
          simp only [hDFshl, hFshl, hDShl, hShl] at h
          by_cases hcond : fx = sx ∧ fy = sy
          · simp only [guard, if_pos hcond, bind, Option.bind, pure, Option.some.injEq] at h
            exact ⟨h.symm, dFshl, fx, fz, fy, dShl, sx, sy, shProps,
              rfl, hFshl, rfl, hShl, hcond.1, hcond.2⟩
          · simp only [guard, if_neg hcond, bind, Option.bind, failure,
              reduceCtorEq] at h

/-- Syntactic decomposition of a successful `funnelOrLshrTryOrder`. -/
private theorem funnelOrLshrTryOrder_some {ctx : WfIRContext OpCode} {fshrV lshrV keep : ValuePtr}
    (h : funnelOrLshrTryOrder ctx fshrV lshrV = some keep) :
    keep = fshrV ∧ ∃ dFshr fz fx fy dLshr sx sy shProps,
      getDefiningOp fshrV ctx = some dFshr ∧ matchFshr dFshr ctx = some (fz, fx, fy) ∧
      getDefiningOp lshrV ctx = some dLshr ∧ matchLshr dLshr ctx = some (sx, sy, shProps) ∧
      fx = sx ∧ fy = sy := by
  rw [funnelOrLshrTryOrder] at h
  cases hDFshr : getDefiningOp fshrV ctx.raw with
  | none => simp [hDFshr] at h
  | some dFshr =>
    cases hFshr : matchFshr dFshr ctx.raw with
    | none => simp [hDFshr, hFshr] at h
    | some triple =>
      obtain ⟨fz, fx, fy⟩ := triple
      cases hDLshr : getDefiningOp lshrV ctx.raw with
      | none => simp [hDFshr, hFshr, hDLshr] at h
      | some dLshr =>
        cases hLshr : matchLshr dLshr ctx.raw with
        | none => simp [hDFshr, hFshr, hDLshr, hLshr] at h
        | some striple =>
          obtain ⟨sx, sy, shProps⟩ := striple
          simp only [hDFshr, hFshr, hDLshr, hLshr] at h
          by_cases hcond : fx = sx ∧ fy = sy
          · simp only [guard, if_pos hcond, bind, Option.bind, pure, Option.some.injEq] at h
            exact ⟨h.symm, dFshr, fz, fx, fy, dLshr, sx, sy, shProps,
              rfl, hFshr, rfl, hLshr, hcond.1, hcond.2⟩
          · simp only [guard, if_neg hcond, bind, Option.bind, failure,
              reduceCtorEq] at h

set_option maxHeartbeats 1000000 in
theorem funnel_shift_or_shift_to_funnel_shift_left_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps funnel_shift_or_shift_to_funnel_shift_left_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges funnel_shift_or_shift_to_funnel_shift_left_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds funnel_shift_or_shift_to_funnel_shift_left_local}
    {h₄ : LocalRewritePattern.ReturnValues funnel_shift_or_shift_to_funnel_shift_left_local} :
    LocalRewritePattern.PreservesSemantics
      funnel_shift_or_shift_to_funnel_shift_left_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics,
    funnel_shift_or_shift_to_funnel_shift_left_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchOr`.
  have hMatchSome : (matchOr op ctx.raw).isSome := by
    cases hM : matchOr op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨o0, o1, orProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hOrPropsEq⟩ := matchOr_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Result-type guard.
  obtain ⟨intType, hResType⟩ :
      ∃ t, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Bitwidth guard.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  -- Verifier facts for the `or`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_or opVerif hOpType
  have hIntEq : opIntType = intType := by
    have h1 : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType := by
      rw [hOpResType]
    rw [hResType] at h1; grind
  have hWidth : opIntType.bitwidth = 64 ∨ opIntType.bitwidth = 32 := by rw [hIntEq]; omega
  have ho0Eq : o0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have ho1Eq : o1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = o0 := by
    rw [ho0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = o1 := by
    rw [ho1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (o0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (o1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer `or`'s interpretation.
  have hSemOr : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm .or))
      (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
      Llvm.interpretOp' .or props rt #[.int bw a, .int bw b] bo mem
        = some (.ok (#[.int bw (Data.LLVM.Int.or a b props.disjoint)], mem, none)) :=
    fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
  obtain ⟨o0v, o1v, ho0Val, ho1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .or)
      (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
      (props := op.getProperties! ctx.raw (.llvm .or))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemOr bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the `.orElse`.
  have hKeepSome : ((funnelOrShlTryOrder ctx o0 o1).or (funnelOrShlTryOrder ctx o1 o0)).isSome := by
    cases hM : (funnelOrShlTryOrder ctx o0 o1).or (funnelOrShlTryOrder ctx o1 o0) with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨keep, hKeep⟩ := Option.isSome_iff_exists.mp hKeepSome
  rw [hKeep] at hpattern
  simp only [] at hpattern
  obtain ⟨hNewCtx, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[keep] := by
    simp at hpattern; grind
  subst newCtx
  -- Common membership facts for the two `or` operands.
  have ho0mem : o0 ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  have ho1mem : o1 ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  -- The interpreter-fact for `fshl` (used by the ternary graph lemma).
  have hSemFshl : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm .intr__fshl))
      (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
      Llvm.interpretOp' .intr__fshl props rt #[.int bw x, .int bw y, .int bw z] bo mem
        = some (.ok (#[.int bw (Data.LLVM.Int.fshl x y z)], mem, none)) :=
    fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
  -- Split the two operand orders.
  rcases hcase : funnelOrShlTryOrder ctx o0 o1 with _ | k0
  · -- Order B: the `fshl` is `o1`, the `shl` is `o0`. `keep = o1`.
    have hSnd : funnelOrShlTryOrder ctx o1 o0 = some keep := by
      rw [hcase] at hKeep; simpa using hKeep
    obtain ⟨hkeepEq, dFshl, fx, fz, fy, dShl, sx, sy, shProps, hDFshl, hFshl, hDShl, hShl,
      hfxsx, hfysy⟩ := funnelOrShlTryOrder_some hSnd
    subst hkeepEq
    -- Recover the `fshl` operands' values (base = `o1`).
    obtain ⟨av, bv, cv, haVal, hbVal, hcVal, hFshlBaseVal⟩ :=
      matchTernaryOp_getVar?_of_EquationLemmaAt
        (srcFn := fun {_} x y z => Data.LLVM.Int.fshl x y z)
        (fun hM => matchFshl_implies hM)
        (fun ov ht => OperationPtr.Verified.llvm_intr__fshl ov ht)
        (fun ht => OperationPtr.Pure.llvm_intr__fshl ht)
        hSemFshl ctxDom ctxVerif opInBounds stateWf hDFshl hFshl ho1mem hv1Type
    -- Recover the `shl` operands' values (base = `o0`).
    obtain ⟨sxv, syv, hsxVal, hsyVal, hShlBaseVal, hsxType, hDomSx, hDomSy, hsxIn, hsyIn,
      sxNotOp, syNotOp⟩ :=
      matchShl_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDShl hShl ho0mem hv0Type
    -- Identify the shared operands.
    have hav : sxv = av := by
      have hh := haVal; rw [hfxsx, hsxVal] at hh; simpa using hh
    have hcv : syv = cv := by
      have hh := hcVal; rw [hfysy, hsyVal] at hh; simpa using hh
    -- `o1v = fshl av bv cv` and `o0v = shl av cv …`.
    have ho1v : o1v = Data.LLVM.Int.fshl av bv cv := by
      have hh := ho1Val.symm.trans hFshlBaseVal; simpa using hh
    have ho0v : o0v = Data.LLVM.Int.shl av cv shProps.nsw shProps.nuw := by
      have hh := ho0Val.symm.trans hShlBaseVal; rw [hav, hcv] at hh; simpa using hh
    -- Read the refined kept value (= `o1`).
    have hKeepDom := ctxDom.operand_dominates_op opInBounds ho1mem
    have hKeepNotOp : keep ∉ op.getResults! ctx.raw := by
      grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
    obtain ⟨kt, hKtVal, hKtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) ho1Val
        hKeepDom hKeepDom hKeepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by
      simp [hKtVal, Option.bind, Option.map], ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    rw [ho0v, ho1v]
    simp only [Data.LLVM.Int.cast_self]
    exact isRefinedBy_trans (Data.LLVM.Int.funnel_shift_or_shl_left_comm hWidth) (ho1v ▸ hKtRef)
  · -- Order A: the `fshl` is `o0`, the `shl` is `o1`. `keep = o0`.
    have hFst : funnelOrShlTryOrder ctx o0 o1 = some keep := by
      rw [hcase] at hKeep ⊢; simpa using hKeep
    obtain ⟨hkeepEq, dFshl, fx, fz, fy, dShl, sx, sy, shProps, hDFshl, hFshl, hDShl, hShl,
      hfxsx, hfysy⟩ := funnelOrShlTryOrder_some hFst
    subst hkeepEq
    obtain ⟨av, bv, cv, haVal, hbVal, hcVal, hFshlBaseVal⟩ :=
      matchTernaryOp_getVar?_of_EquationLemmaAt
        (srcFn := fun {_} x y z => Data.LLVM.Int.fshl x y z)
        (fun hM => matchFshl_implies hM)
        (fun ov ht => OperationPtr.Verified.llvm_intr__fshl ov ht)
        (fun ht => OperationPtr.Pure.llvm_intr__fshl ht)
        hSemFshl ctxDom ctxVerif opInBounds stateWf hDFshl hFshl ho0mem hv0Type
    obtain ⟨sxv, syv, hsxVal, hsyVal, hShlBaseVal, hsxType, hDomSx, hDomSy, hsxIn, hsyIn,
      sxNotOp, syNotOp⟩ :=
      matchShl_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDShl hShl ho1mem hv1Type
    have hav : sxv = av := by
      have hh := haVal; rw [hfxsx, hsxVal] at hh; simpa using hh
    have hcv : syv = cv := by
      have hh := hcVal; rw [hfysy, hsyVal] at hh; simpa using hh
    have ho0v : o0v = Data.LLVM.Int.fshl av bv cv := by
      have hh := ho0Val.symm.trans hFshlBaseVal; simpa using hh
    have ho1v : o1v = Data.LLVM.Int.shl av cv shProps.nsw shProps.nuw := by
      have hh := ho1Val.symm.trans hShlBaseVal; rw [hav, hcv] at hh; simpa using hh
    have hKeepDom := ctxDom.operand_dominates_op opInBounds ho0mem
    have hKeepNotOp : keep ∉ op.getResults! ctx.raw := by
      grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
    obtain ⟨kt, hKtVal, hKtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) ho0Val
        hKeepDom hKeepDom hKeepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by
      simp [hKtVal, Option.bind, Option.map], ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    rw [ho0v, ho1v]
    simp only [Data.LLVM.Int.cast_self]
    exact isRefinedBy_trans (Data.LLVM.Int.funnel_shift_or_shl_left hWidth) (ho0v ▸ hKtRef)

set_option maxHeartbeats 1000000 in
theorem funnel_shift_or_shift_to_funnel_shift_right_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps funnel_shift_or_shift_to_funnel_shift_right_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges funnel_shift_or_shift_to_funnel_shift_right_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds funnel_shift_or_shift_to_funnel_shift_right_local}
    {h₄ : LocalRewritePattern.ReturnValues funnel_shift_or_shift_to_funnel_shift_right_local} :
    LocalRewritePattern.PreservesSemantics
      funnel_shift_or_shift_to_funnel_shift_right_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics,
    funnel_shift_or_shift_to_funnel_shift_right_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel the outer `matchOr`.
  have hMatchSome : (matchOr op ctx.raw).isSome := by
    cases hM : matchOr op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨o0, o1, orProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hOrPropsEq⟩ := matchOr_implies hMatch
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Result-type guard.
  obtain ⟨intType, hResType⟩ :
      ∃ t, ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hResType] at hpattern
  simp only [] at hpattern
  -- Bitwidth guard.
  split at hpattern
  case isTrue => simp at hpattern
  rename_i hWidthRaw
  -- Verifier facts for the `or`.
  have opVerif : op.Verified ctx opInBounds := by grind
  obtain ⟨-, -, -, -, opIntType, hOpResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_or opVerif hOpType
  have hIntEq : opIntType = intType := by
    have h1 : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType opIntType := by
      rw [hOpResType]
    rw [hResType] at h1; grind
  have hWidth : opIntType.bitwidth = 64 ∨ opIntType.bitwidth = 32 := by rw [hIntEq]; omega
  have ho0Eq : o0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have ho1Eq : o1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = o0 := by
    rw [ho0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = o1 := by
    rw [ho1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0Type : (o0.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand0, hOp0Type]
  have hv1Type : (o1.getType! ctx.raw).val = Attribute.integerType opIntType := by
    rw [← hOperand1, hOp1Type]
  -- Unfold the outer `or`'s interpretation.
  have hSemOr : ∀ (bw : Nat) (a b : Data.LLVM.Int bw) (props : propertiesOf (.llvm .or))
      (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
      Llvm.interpretOp' .or props rt #[.int bw a, .int bw b] bo mem
        = some (.ok (#[.int bw (Data.LLVM.Int.or a b props.disjoint)], mem, none)) :=
    fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
  obtain ⟨o0v, o1v, ho0Val, ho1Val, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .or)
      (srcFn := fun a b p => Data.LLVM.Int.or a b p.disjoint)
      (props := op.getProperties! ctx.raw (.llvm .or))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          rw [hSemOr bw a b props resultTypes blockOperands mem] at hh
          injection hh with hh; injection hh with hh; exact hh.symm)
      hinterp hv0Type hv1Type
  subst hCf
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Peel the `.orElse` (simplified by the initial `simp` to `Option.or`).
  have hKeepSome : ((funnelOrLshrTryOrder ctx o0 o1).or
      (funnelOrLshrTryOrder ctx o1 o0)).isSome := by
    cases hM : (funnelOrLshrTryOrder ctx o0 o1).or (funnelOrLshrTryOrder ctx o1 o0) with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨keep, hKeep⟩ := Option.isSome_iff_exists.mp hKeepSome
  rw [hKeep] at hpattern
  simp only [] at hpattern
  obtain ⟨hNewCtx, rfl, rfl⟩ : newCtx = ctx ∧ newOps = #[] ∧ newValues = #[keep] := by
    simp at hpattern; grind
  subst newCtx
  have ho0mem : o0 ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  have ho1mem : o1 ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  -- The interpreter-fact for `fshr` (used by the ternary graph lemma).
  have hSemFshr : ∀ (bw : Nat) (x y z : Data.LLVM.Int bw) (props : propertiesOf (.llvm .intr__fshr))
      (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
      Llvm.interpretOp' .intr__fshr props rt #[.int bw x, .int bw y, .int bw z] bo mem
        = some (.ok (#[.int bw (Data.LLVM.Int.fshr x y z)], mem, none)) :=
    fun _ _ _ _ _ _ _ => by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
  -- Split the two operand orders.
  rcases hcase : funnelOrLshrTryOrder ctx o0 o1 with _ | k0
  · -- Order B: the `fshr` is `o1`, the `lshr` is `o0`. `keep = o1`.
    have hSnd : funnelOrLshrTryOrder ctx o1 o0 = some keep := by
      rw [hcase] at hKeep; simpa using hKeep
    obtain ⟨hkeepEq, dFshr, fz, fx, fy, dLshr, sx, sy, shProps, hDFshr, hFshr, hDLshr, hLshr,
      hfxsx, hfysy⟩ := funnelOrLshrTryOrder_some hSnd
    subst hkeepEq
    -- Recover the `fshr` operands' values (base = `o1`).
    obtain ⟨av, bv, cv, haVal, hbVal, hcVal, hFshrBaseVal⟩ :=
      matchTernaryOp_getVar?_of_EquationLemmaAt
        (srcFn := fun {_} x y z => Data.LLVM.Int.fshr x y z)
        (fun hM => matchFshr_implies hM)
        (fun ov ht => OperationPtr.Verified.llvm_intr__fshr ov ht)
        (fun ht => OperationPtr.Pure.llvm_intr__fshr ht)
        hSemFshr ctxDom ctxVerif opInBounds stateWf hDFshr hFshr ho1mem hv1Type
    -- Recover the `lshr` operands' values (base = `o0`).
    obtain ⟨shType, xv, sv, h', hxVal, hsvVal, hLshrBaseVal, hxType, hsType, hDomX, hDomS,
      hxIn, hsIn, xNotOp, sNotOp⟩ :=
      matchLshr_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDLshr hLshr ho0mem hv0Type
    -- Identify the shared operands (`fshr`'s data operand `fx` = `lshr`'s base `sx`, `fy` = `sy`).
    have hxvbv : xv = bv := by
      have hh := hbVal; rw [hfxsx, hxVal] at hh; simpa using hh
    have hcvsv : h' ▸ sv = cv := by
      have hh := hsvVal; rw [← hfysy, hcVal] at hh
      injection hh with hh; injection hh with hw hheq
      exact eq_of_heq ((eqRec_heq h' sv).trans (HEq.symm hheq))
    have ho1v : o1v = Data.LLVM.Int.fshr av bv cv := by
      have hh := ho1Val.symm.trans hFshrBaseVal; simpa using hh
    have ho0v : o0v = Data.LLVM.Int.lshr bv cv shProps.exact := by
      have hh := ho0Val.symm.trans hLshrBaseVal; rw [hxvbv, hcvsv] at hh; simpa using hh
    -- Read the refined kept value (= `o1`).
    have hKeepDom := ctxDom.operand_dominates_op opInBounds ho1mem
    have hKeepNotOp : keep ∉ op.getResults! ctx.raw := by
      grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
    obtain ⟨kt, hKtVal, hKtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) ho1Val
        hKeepDom hKeepDom hKeepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by
      simp [hKtVal, Option.bind, Option.map], ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    rw [ho0v, ho1v]
    simp only [Data.LLVM.Int.cast_self]
    exact isRefinedBy_trans (Data.LLVM.Int.funnel_shift_or_lshr_right_comm hWidth) (ho1v ▸ hKtRef)
  · -- Order A: the `fshr` is `o0`, the `lshr` is `o1`. `keep = o0`.
    have hFst : funnelOrLshrTryOrder ctx o0 o1 = some keep := by
      rw [hcase] at hKeep ⊢; simpa using hKeep
    obtain ⟨hkeepEq, dFshr, fz, fx, fy, dLshr, sx, sy, shProps, hDFshr, hFshr, hDLshr, hLshr,
      hfxsx, hfysy⟩ := funnelOrLshrTryOrder_some hFst
    subst hkeepEq
    obtain ⟨av, bv, cv, haVal, hbVal, hcVal, hFshrBaseVal⟩ :=
      matchTernaryOp_getVar?_of_EquationLemmaAt
        (srcFn := fun {_} x y z => Data.LLVM.Int.fshr x y z)
        (fun hM => matchFshr_implies hM)
        (fun ov ht => OperationPtr.Verified.llvm_intr__fshr ov ht)
        (fun ht => OperationPtr.Pure.llvm_intr__fshr ht)
        hSemFshr ctxDom ctxVerif opInBounds stateWf hDFshr hFshr ho0mem hv0Type
    obtain ⟨shType, xv, sv, h', hxVal, hsvVal, hLshrBaseVal, hxType, hsType, hDomX, hDomS,
      hxIn, hsIn, xNotOp, sNotOp⟩ :=
      matchLshr_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDLshr hLshr ho1mem hv1Type
    have hxvbv : xv = bv := by
      have hh := hbVal; rw [hfxsx, hxVal] at hh; simpa using hh
    have hcvsv : h' ▸ sv = cv := by
      have hh := hsvVal; rw [← hfysy, hcVal] at hh
      injection hh with hh; injection hh with hw hheq
      exact eq_of_heq ((eqRec_heq h' sv).trans (HEq.symm hheq))
    have ho0v : o0v = Data.LLVM.Int.fshr av bv cv := by
      have hh := ho0Val.symm.trans hFshrBaseVal; simpa using hh
    have ho1v : o1v = Data.LLVM.Int.lshr bv cv shProps.exact := by
      have hh := ho1Val.symm.trans hLshrBaseVal; rw [hxvbv, hcvsv] at hh; simpa using hh
    have hKeepDom := ctxDom.operand_dominates_op opInBounds ho0mem
    have hKeepNotOp : keep ∉ op.getResults! ctx.raw := by
      grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
    obtain ⟨kt, hKtVal, hKtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) ho0Val
        hKeepDom hKeepDom hKeepNotOp
    refine ⟨state', by
      simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
    refine ⟨#[RuntimeValue.int opIntType.bitwidth kt], by
      simp [hKtVal, Option.bind, Option.map], ?_⟩
    refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
    rw [ho0v, ho1v]
    simp only [Data.LLVM.Int.cast_self]
    exact isRefinedBy_trans (Data.LLVM.Int.funnel_shift_or_lshr_right hWidth) (ho0v ▸ hKtRef)

/-! ### ext_li_range :  riscv.<ext> (riscv.li v) → riscv.li v   when `lo ≤ v < hi`

  Combines the outer-`ext` handling of the idempotent-extension folds
  (`matchRiscvUnaryReg_interpretOp_unfold`) with the defining-`riscv.li` handling of
  `right_identity_zero_add` (`riscvLiOp_interpretOp_unfold`): the outer unary register op `ext`
  reads a single operand whose defining `riscv.li` materialises `Data.RISCV.li (BitVec.ofInt 64 v)`.
  RISC-V register values are total (no poison), so the obligation collapses to the register equality
  `f (li (ofInt 64 v)) = li (ofInt 64 v)`, supplied by `hData` on the guard range `[lo, hi)` (the
  `Int`-range data lemmas `Data.RISCV.{zextb,zexth,zextw,sextb,sexth,sextw}_li_ofInt` in `Proofs.lean`,
  which bridge the immediate's `Int` bound to the materialised value's bit pattern). -/

set_option maxHeartbeats 1000000 in
/-- Shared correctness for the `riscv.<ext> (riscv.li v) -> riscv.li v` fold, over any unary
    reg-to-reg `riscv` op `ext` (data action `f`, characterised by `hSem` as in
    `drop_redundant_ext_local_preservesSemantics`) that is the identity on `Data.RISCV.li
    (BitVec.ofInt 64 v)` for every `v ∈ [lo, hi)` (`hData`). No ops are created; `op`'s result is
    forwarded to its `li`-defined operand, and the dropped result `f (li (ofInt 64 v))` matches it by
    `hData` — an exact equality, since registers carry no poison. -/
theorem ext_li_range_local_preservesSemantics {ext : Riscv} {lo hi : Int}
    {f : Data.RISCV.Reg → Data.RISCV.Reg}
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (f r)], mem, none))
    (hData : ∀ v : Int, lo ≤ v → v < hi →
        f (Data.RISCV.li (BitVec.ofInt 64 v)) = Data.RISCV.li (BitVec.ofInt 64 v))
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local ext lo hi)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local ext lo hi)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local ext lo hi)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local ext lo hi)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local ext lo hi) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, ext_li_range_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp (.riscv ext) 1`.
  have hMatchSome : (matchOp op ctx.raw (.riscv ext) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv ext) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, oProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp operands[0]!` (the defining `li`).
  have hDefSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨liOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  -- Peel the inner `matchOp (.riscv .li) 0`.
  have hLiSome : (matchOp liOp ctx.raw (.riscv .li) 0).isSome := by
    cases hIM : matchOp liOp ctx.raw (.riscv .li) 0 with
    | some y => rfl
    | none => rw [hIM] at hpattern; simp at hpattern
  obtain ⟨⟨liOperands, cst⟩, hLiMatch⟩ := Option.isSome_iff_exists.mp hLiSome
  obtain ⟨hLiType, -, hLiNumResults, -, hLiProps⟩ := matchOp_implies hLiMatch
  rw [hLiMatch] at hpattern
  simp only [] at hpattern
  -- The `[lo, hi)` guard: the true branch cannot equal a `some (_, some _)`.
  split at hpattern
  · simp at hpattern
  rename_i hcond
  have hlo : lo ≤ cst.value.value := by omega
  have hhi : cst.value.value < hi := by omega
  -- Read off the pattern outputs: nothing is created, the result forwards to `operands[0]!`.
  obtain ⟨rfl, rfl, rfl⟩ : ctx = newCtx ∧ newOps = #[] ∧ newValues = #[operands[0]!] := by
    simp at hpattern; grind
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, -⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  -- Unfold the outer ext op's interpretation.
  obtain ⟨v, hOuterSrcVal, hMem, hResVal, hCf⟩ :=
    matchRiscvUnaryReg_interpretOp_unfold (rop := ext) (f := f) opInBounds hOpType hNumResults
      hOperands hSem hinterp
  subst hCf
  -- The forwarded operand is defined by the `li`; recover the value it materialises.
  obtain ⟨liPtr, hSrcPtr, hLiOpEq⟩ :
      ∃ p, operands[0]! = ValuePtr.opResult p ∧ p.op = liOp := by
    match hm : operands[0]! with
    | .opResult p => exact ⟨p, rfl, by rw [hm] at hDef; simpa [getDefiningOp] using hDef⟩
    | .blockArgument p => rw [hm] at hDef; simp [getDefiningOp] at hDef
  subst hLiOpEq
  have hSrcMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  have hSrcIn : operands[0]!.InBounds ctx.raw := by grind
  have hLiOpIn : liPtr.op.InBounds ctx.raw := by
    rw [hSrcPtr] at hSrcIn; grind [OpResultPtr.InBounds]
  have hLiIdx : liPtr.index < liPtr.op.getNumResults! ctx.raw := by
    rw [hSrcPtr] at hSrcIn
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!, OpResultPtr.InBounds]
  have hLiEq : liPtr = liPtr.op.getResult 0 := by
    have hidx : liPtr.index = 0 := by omega
    cases liPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hLiDefines : (ValuePtr.opResult liPtr).getDefiningOp! ctx.raw = some liPtr.op := by
    have hOwner := (ctx.wellFormed.operations liPtr.op hLiOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hLiSDom : liPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hLiDefines (by rw [← hSrcPtr]; exact hSrcMem)
  have hLiDomIp : liPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hLiPure : liPtr.op.Pure ctx.raw := riscv_li_pure hLiType
  obtain ⟨cfLi, hInterpLi⟩ := stateWf liPtr.op hLiOpIn hLiPure hLiDomIp
  have hLiVal := riscvLiOp_interpretOp_unfold hLiOpIn hLiType hLiNumResults hInterpLi
  have hCstVal : (liPtr.op.getProperties! ctx.raw (.riscv .li)).value.value = cst.value.value := by
    rw [hLiProps]
  rw [hCstVal] at hLiVal
  have hSrcVal2 : state.variables.getVar? operands[0]!
      = some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 cst.value.value))) := by
    rw [hSrcPtr, hLiEq]; exact hLiVal
  obtain rfl : v = Data.RISCV.li (BitVec.ofInt 64 cst.value.value) := by
    have := hOuterSrcVal.symm.trans hSrcVal2; simpa using this
  -- `sourceValues` is the single dropped result value `.reg (f (li (ofInt 64 v)))`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- The forwarded operand dominates the match point and is not one of `op`'s results.
  have hDomSrc : (operands[0]!).dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hSrcNotOp : ¬ operands[0]! ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Read the forwarded operand's value in the target state (register refinement is equality).
  have hSrcTgt :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom (by grind)
      hOuterSrcVal hDomSrc hDomSrc hSrcNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 cst.value.value))], by
    simp [hSrcTgt, Option.bind, Option.map], ?_⟩
  exact RuntimeValue.arrayIsRefinedBy_singleton.mpr (hData cst.value.value hlo hhi)

theorem zextb_li_low8_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .zextb 0 256)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .zextb 0 256)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .zextb 0 256)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .zextb 0 256)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local .zextb 0 256) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.zextb)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.zextb_li_ofInt h0 h1)

theorem zexth_li_low16_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .zexth 0 65536)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .zexth 0 65536)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .zexth 0 65536)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .zexth 0 65536)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local .zexth 0 65536) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.zexth)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.zexth_li_ofInt h0 h1)

theorem zextw_li_low32_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .zextw 0 4294967296)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .zextw 0 4294967296)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .zextw 0 4294967296)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .zextw 0 4294967296)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local .zextw 0 4294967296) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.zextw)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.zextw_li_ofInt h0 h1)

theorem sextb_li_low8_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .sextb (-128) 128)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .sextb (-128) 128)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .sextb (-128) 128)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .sextb (-128) 128)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local .sextb (-128) 128) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.sextb)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.sextb_li_ofInt h0 h1)

theorem sexth_li_low16_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .sexth (-32768) 32768)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .sexth (-32768) 32768)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .sexth (-32768) 32768)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .sexth (-32768) 32768)} :
    LocalRewritePattern.PreservesSemantics (ext_li_range_local .sexth (-32768) 32768) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.sexth)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.sexth_li_ofInt h0 h1)

theorem sextw_li_low32_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (ext_li_range_local .sextw (-2147483648) 2147483648)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (ext_li_range_local .sextw (-2147483648) 2147483648)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (ext_li_range_local .sextw (-2147483648) 2147483648)}
    {h₄ : LocalRewritePattern.ReturnValues (ext_li_range_local .sextw (-2147483648) 2147483648)} :
    LocalRewritePattern.PreservesSemantics
      (ext_li_range_local .sextw (-2147483648) 2147483648) h h₂ h₃ h₄ :=
  ext_li_range_local_preservesSemantics
    (f := Data.RISCV.sextw)
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ h0 h1 => Veir.Data.RISCV.sextw_li_ofInt h0 h1)

/-! ### li_zero_to_x0 :  riscv.li 0 → rv64.get_register x0

  Matches `riscv.li 0` and, when it has uses, creates an `rv64.get_register` with a `!riscv.reg<x0>`
  result and forwards the `li`'s result to it. Unlike the other create-and-replay combines this one
  materializes a *nullary* op: `rv64.get_register` reads the hard-wired zero register `x0` as `⟨0⟩`
  (`interpretOp_rv64_get_register_forward`), which matches what `riscv.li 0` materializes,
  `RISCV.li (BitVec.ofInt 64 0) = ⟨0⟩` (`li_zero_eq_x0`). Register refinement is equality (no poison),
  so the obligation is that exact equality. The `!op.hasUses!` guard is peeled but plays no role in
  the semantic argument. -/

set_option maxHeartbeats 1000000 in
theorem li_zero_to_x0_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps li_zero_to_x0_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges li_zero_to_x0_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds li_zero_to_x0_local}
    {h₄ : LocalRewritePattern.ReturnValues li_zero_to_x0_local} :
    LocalRewritePattern.PreservesSemantics li_zero_to_x0_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, li_zero_to_x0_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchOp op (.riscv .li) 0`.
  have hMatchSome : (matchOp op ctx.raw (.riscv .li) 0).isSome := by
    cases hM : matchOp op ctx.raw (.riscv .li) 0 with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨liOperands, cst⟩, hLiMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hLiType, -, hLiNumResults, -, hLiProps⟩ := matchOp_implies hLiMatch
  rw [hLiMatch] at hpattern
  simp only [] at hpattern
  -- The `cst.value.value ≠ 0` guard.
  have hCst0 : cst.value.value = 0 := by
    split at hpattern
    · assumption
    · simp at hpattern
  rw [if_pos hCst0] at hpattern
  have hCstVal0 : (op.getProperties! ctx.raw (.riscv .li)).value.value = 0 := by
    rw [hLiProps] at hCst0; exact hCst0
  -- The `!op.hasUses!` guard (semantically irrelevant; keep only the live branch).
  have hUsesFalse : ¬ (op.hasUses! ctx.raw = false) := by
    intro hf; rw [if_pos hf] at hpattern; simp at hpattern
  rw [if_neg hUsesFalse] at hpattern
  -- The `li`'s runtime value.
  have hLiVal := riscvLiOp_interpretOp_unfold opInBounds hLiType hLiNumResults hinterp
  -- `cf = none` and memory is unchanged by the `li`.
  obtain ⟨hCfNone, hMemNew⟩ : cf = none ∧ newState.memory = state.memory := by
    rw [interpretOp_some_iff] at hinterp
    obtain ⟨_, resValues, mem', varState', _, hInterp', _, hNew⟩ := hinterp
    simp only [OperationPtr.interpret] at hInterp'
    rw [hLiType] at hInterp'
    simp only [interpretOp', Riscv.interpretOp', pure, Interp] at hInterp'
    subst hNew; grind
  subst hCfNone
  -- Source value: the dropped `li 0` result.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hLiVal] at hsourceValues
  subst sourceValues
  -- Peel the single `rv64.get_register` creation.
  peelOpCreation hpattern ctx₁ x0Op hCreate
  cleanupHpattern hpattern
  replace hCreate := WfRewriter.createOp!_none_some hCreate
  obtain ⟨_, _, _, hCreate⟩ := hCreate
  -- Structural facts for the created `get_register`.
  have hX0Type : x0Op.getOpType! ctx₁.raw = .rv64 .get_register := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hCreate (operation := x0Op)]
  have hX0Operands : x0Op.getOperands! ctx₁.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCreate (operation := x0Op)]
  have hX0ResTypes : x0Op.getResultTypes! ctx₁.raw
      = #[(RegisterType.mk (some 0) : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hCreate (operation := x0Op)
    rw [if_pos rfl] at hT; exact hT
  -- Replay the `get_register` in the target state.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_rv64_get_register_forward (state := state') (inBounds := by grind)
      hX0Type hX0Operands hX0ResTypes rfl
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.reg ⟨0⟩], by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  simp only [RuntimeValue.isRefinedBy]
  rw [hCstVal0]
  first | exact Data.RISCV.li_ofInt_zero_eq_x0 | exact Data.RISCV.li_ofInt_zero_eq_x0.symm

/-! ### `drop_ext_of_bitwise` : drop `riscv.<ext>` wrapping a guarded bitwise op

  `op` is a `riscv.<ext>` whose operand `inner` is defined by a bitwise `riscv.<dst>` (`and`/`or`/
  `xor`). No operation is created: the `<ext>`'s result is replaced by `inner`. The inner op's two
  operands are recovered with `riscv_binaryReg_getVar?_of_EquationLemmaAt`; when the `definedByExt`
  guard reports an operand is itself defined by a `riscv.<ext>`, that operand's value is pinned to the
  image of the extension with `riscv_unaryReg_getVar?_of_strictlyDominates` (the operand's defining
  ext op strictly dominates `op` by transitivity through the inner op). The obligation then collapses
  to the width-generic `Reg` equalities in `Proofs.lean` (`zextw_and_left`/`_right`, `zextw_or`, …),
  which encode exactly why one guarded operand suffices for `and` under a zero-extension but both are
  needed for `or`/`xor` and every sign-extension. -/

/-- If the `definedByExt` guard fires for `v`, recover the defining `riscv.<ext>` op and its match. -/
private theorem definedByExt_of_eq_true {ext : Riscv} {v : ValuePtr} {ctx : IRContext OpCode}
    (h : definedByExt ext v ctx = true) :
    ∃ d eops eprops, getDefiningOp v ctx = some d ∧
      matchOp d ctx (.riscv ext) 1 = some (eops, eprops) := by
  unfold definedByExt at h
  cases hd : getDefiningOp v ctx with
  | none => simp [hd] at h
  | some d =>
    cases hm : matchOp d ctx (.riscv ext) 1 with
    | none => simp [hd, hm] at h
    | some p =>
      obtain ⟨eops, eprops⟩ := p
      exact ⟨d, eops, eprops, rfl, hm⟩

set_option maxHeartbeats 1000000 in
/-- Shared correctness for `drop_ext_of_bitwise_local`, generic over the extension `ext` (with data
    action `fext`), the bitwise op `dst` (with data action `fdst`), and the `oneOperandSuffices`
    flag. The data obligation `fext (fdst r₁ r₂) = fdst r₁ r₂` is supplied per guard scenario:
    `hDataL`/`hDataR` cover a single guarded operand (only sound when `oneOperandSuffices`), and
    `hDataBoth` covers both operands guarded (used when both are required). Each is guarded by the
    flag value so that the vacuous scenario is discharged trivially at instantiation. -/
theorem drop_ext_of_bitwise_local_preservesSemantics {ext dst : Riscv} {oneOperandSuffices : Bool}
    {fext : Data.RISCV.Reg → Data.RISCV.Reg}
    {fdst : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hPureExt : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv ext → opp.Pure c)
    (hSemExt : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (fext r)], mem, none))
    (hPureDst : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv dst → opp.Pure c)
    (hSemDst : ∀ (props : HasDialectOpInfo.propertiesOf dst) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' dst props rt ops bo mem = some (.ok res) →
        ∃ r₁ r₂, ops = #[.reg r₁, .reg r₂] ∧ res = (#[.reg (fdst r₁ r₂)], mem, none))
    (hDataL : oneOperandSuffices = true →
        ∀ (a r₂ : Data.RISCV.Reg), fext (fdst (fext a) r₂) = fdst (fext a) r₂)
    (hDataR : oneOperandSuffices = true →
        ∀ (r₁ b : Data.RISCV.Reg), fext (fdst r₁ (fext b)) = fdst r₁ (fext b))
    (hDataBoth : oneOperandSuffices = false →
        ∀ (a b : Data.RISCV.Reg), fext (fdst (fext a) (fext b)) = fdst (fext a) (fext b))
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local ext dst oneOperandSuffices)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local ext dst oneOperandSuffices)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local ext dst oneOperandSuffices)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local ext dst oneOperandSuffices)} :
    LocalRewritePattern.PreservesSemantics
      (drop_ext_of_bitwise_local ext dst oneOperandSuffices) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, drop_ext_of_bitwise_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp`.
  have hMatchSome : (matchOp op ctx.raw (.riscv ext) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv ext) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, oProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Peel `getDefiningOp`.
  have hDefSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨innerOp, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  -- Peel the inner `matchOp`.
  have hInnerMatchSome : (matchOp innerOp ctx.raw (.riscv dst) 2).isSome := by
    cases hIM : matchOp innerOp ctx.raw (.riscv dst) 2 with
    | some y => rfl
    | none => rw [hIM] at hpattern; simp at hpattern
  obtain ⟨⟨innerOperands, iProps⟩, hInnerMatch⟩ := Option.isSome_iff_exists.mp hInnerMatchSome
  rw [hInnerMatch] at hpattern
  simp only [] at hpattern
  -- The guard must hold, else the pattern would have returned `(ctx, none)`.
  have hguard : (if oneOperandSuffices
      then definedByExt ext innerOperands[0]! ctx.raw || definedByExt ext innerOperands[1]! ctx.raw
      else definedByExt ext innerOperands[0]! ctx.raw && definedByExt ext innerOperands[1]! ctx.raw)
      = true := by
    rcases Decidable.em ((if oneOperandSuffices
        then definedByExt ext innerOperands[0]! ctx.raw || definedByExt ext innerOperands[1]! ctx.raw
        else definedByExt ext innerOperands[0]! ctx.raw && definedByExt ext innerOperands[1]! ctx.raw)
        = true) with hg | hg
    · exact hg
    · rw [Bool.not_eq_true] at hg; rw [hg] at hpattern; simp at hpattern
  rw [hguard] at hpattern
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, -⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  obtain ⟨rfl, rfl, rfl⟩ : ctx = newCtx ∧ newOps = #[] ∧ newValues = #[operands[0]!] := by
    simp at hpattern; grind
  -- Unfold the outer op's interpretation.
  obtain ⟨v, hOuterSrcVal, hMem, hResVal, hCf⟩ :=
    matchRiscvUnaryReg_interpretOp_unfold (rop := ext) (f := fext) opInBounds hOpType hNumResults
      hOperands hSemExt hinterp
  subst hCf
  have hDomOuter : (operands[0]!).dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hOuterNotOp : ¬ operands[0]! ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Recover the inner bitwise op's operands and its value `fdst r₁ r₂`.
  obtain ⟨r₁, r₂, hr1, hr2, hBaseVal, hIn0, hIn1, hMem0, hMem1, hInnerSDom⟩ :=
    riscv_binaryReg_getVar?_of_EquationLemmaAt (rop := dst) (f := fdst) ctxDom ctxVerif opInBounds
      stateWf hPureDst hSemDst hDef hInnerMatch (by simp [hOperands])
  obtain rfl : v = fdst r₁ r₂ := by
    have := hOuterSrcVal.symm.trans hBaseVal; simpa using this
  -- The dropped `fext` is a no-op on `fdst r₁ r₂` under the guard.
  have heq : fext (fdst r₁ r₂) = fdst r₁ r₂ := by
    -- Recover an operand's value as the image of `fext` from its `definedByExt` guard.
    have recover : ∀ {idx : Nat} (base : ValuePtr) (rbase : Data.RISCV.Reg),
        base = innerOperands[idx]! →
        state.variables.getVar? base = some (RuntimeValue.reg rbase) →
        base.InBounds ctx.raw → base ∈ innerOp.getOperands! ctx.raw →
        definedByExt ext base ctx.raw = true →
        ∃ a, rbase = fext a := by
      intro idx base rbase _hidx hbaseVal hbaseIn hbaseMem hguardBase
      obtain ⟨defOp, eops, eprops, hDefGet, hDefMatch⟩ := definedByExt_of_eq_true hguardBase
      have hDefRes : defOp.getNumResults! ctx.raw = 1 := (matchOp_implies hDefMatch).2.2.1
      have hDefines : base.getDefiningOp! ctx.raw = some defOp :=
        getDefiningOp!_of_getDefiningOp hDefGet hbaseIn hDefRes
      have hDefSDom : defOp.strictlyDominates op ctx :=
        OperationPtr.strictlyDominates_trans
          (OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hDefines hbaseMem)
          hInnerSDom
      obtain ⟨a, hva⟩ := riscv_unaryReg_getVar?_of_strictlyDominates (rop := ext) (f := fext)
        opInBounds stateWf hPureExt hSemExt hDefGet hDefMatch hbaseIn hDefSDom
      refine ⟨a, ?_⟩
      have := hbaseVal.symm.trans hva; simpa using this
    rcases Decidable.em (oneOperandSuffices = true) with hone | hone
    · rw [hone] at hguard; simp only [if_true, Bool.or_eq_true] at hguard
      rcases hguard with hlg | hrg
      · obtain ⟨a, rfl⟩ := recover innerOperands[0]! r₁ rfl hr1 hIn0 hMem0 hlg
        exact hDataL hone a r₂
      · obtain ⟨b, rfl⟩ := recover innerOperands[1]! r₂ rfl hr2 hIn1 hMem1 hrg
        exact hDataR hone r₁ b
    · rw [Bool.not_eq_true] at hone
      rw [hone] at hguard; simp only [Bool.false_eq_true, if_false, Bool.and_eq_true] at hguard
      obtain ⟨hlg, hrg⟩ := hguard
      obtain ⟨a, rfl⟩ := recover innerOperands[0]! r₁ rfl hr1 hIn0 hMem0 hlg
      obtain ⟨b, rfl⟩ := recover innerOperands[1]! r₂ rfl hr2 hIn1 hMem1 hrg
      exact hDataBoth hone a b
  -- `sourceValues` is the single dropped result value `.reg (fext (fdst r₁ r₂))`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Read the forwarded operand's value in the target state (register refinement is equality).
  have hOuterTgt :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom (by grind)
      hOuterSrcVal hDomOuter hDomOuter hOuterNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.reg (fdst r₁ r₂)], by simp [hOuterTgt, Option.bind, Option.map], ?_⟩
  exact RuntimeValue.arrayIsRefinedBy_singleton.mpr heq

/-! Per-opcode characterisations of the `riscv` unary-extension and binary-bitwise interpreters,
    plus the 14 instantiations of `drop_ext_of_bitwise_local_preservesSemantics`. -/

private theorem char_zextw : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.zextw) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.zextw props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.zextw r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_sextw : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.sextw) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.sextw props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.sextw r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_zextb : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.zextb) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.zextb props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.zextb r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_zexth : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.zexth) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.zexth props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.zexth r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_sextb : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.sextb) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.sextb props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.sextb r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_sexth : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.sexth) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.sexth props rt ops bo mem = some (.ok res) →
    ∃ r, ops = #[.reg r] ∧ res = (#[.reg (Data.RISCV.sexth r)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i r heq
    exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_and : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.and) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.and props rt ops bo mem = some (.ok res) →
    ∃ r₁ r₂, ops = #[.reg r₁, .reg r₂] ∧ res = (#[.reg (Data.RISCV.and r₂ r₁)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i op1 op2 heq
    exact ⟨op1, op2, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_or : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.or) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.or props rt ops bo mem = some (.ok res) →
    ∃ r₁ r₂, ops = #[.reg r₁, .reg r₂] ∧ res = (#[.reg (Data.RISCV.or r₂ r₁)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i op1 op2 heq
    exact ⟨op1, op2, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

private theorem char_xor : ∀ (props : HasDialectOpInfo.propertiesOf Riscv.xor) (rt : Array TypeAttr)
    (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
    (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
    Riscv.interpretOp' Riscv.xor props rt ops bo mem = some (.ok res) →
    ∃ r₁ r₂, ops = #[.reg r₁, .reg r₂] ∧ res = (#[.reg (Data.RISCV.xor r₂ r₁)], mem, none) := by
  intro _ _ _ _ _ _ h
  simp only [Riscv.interpretOp', pure, Interp] at h
  split at h
  · rename_i op1 op2 heq
    exact ⟨op1, op2, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
  · exact absurd h (by simp)

theorem zextw_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextw .and true)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextw .and true)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextw .and true)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextw .and true)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextw .and true) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextw) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextw hType) char_zextw
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun _ a r₂ => Data.RISCV.zextw_and_right (a := r₂) (b := a))
    (fun _ r₁ b => Data.RISCV.zextw_and_left (a := b) (b := r₁))
    (fun h => absurd h (by decide))

theorem zextw_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextw .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextw .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextw .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextw .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextw .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextw) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextw hType) char_zextw
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zextw_or (a := b) (b := a))

theorem zextw_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextw .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextw .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextw .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextw .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextw .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextw) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextw hType) char_zextw
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zextw_xor (a := b) (b := a))

theorem sextw_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextw .and false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextw .and false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextw .and false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextw .and false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextw .and false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextw) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextw hType) char_sextw
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextw_and (a := b) (b := a))

theorem sextw_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextw .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextw .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextw .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextw .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextw .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextw) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextw hType) char_sextw
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextw_or (a := b) (b := a))

theorem sextw_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextw .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextw .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextw .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextw .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextw .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextw) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextw hType) char_sextw
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextw_xor (a := b) (b := a))

theorem zextb_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextb .and true)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextb .and true)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextb .and true)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextb .and true)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextb .and true) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextb) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextb hType) char_zextb
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun _ a r₂ => Data.RISCV.zextb_and_right (a := r₂) (b := a))
    (fun _ r₁ b => Data.RISCV.zextb_and_left (a := b) (b := r₁))
    (fun h => absurd h (by decide))

theorem zextb_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextb .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextb .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextb .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextb .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextb .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextb) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextb hType) char_zextb
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zextb_or (a := b) (b := a))

theorem zextb_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zextb .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zextb .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zextb .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zextb .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zextb .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zextb) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zextb hType) char_zextb
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zextb_xor (a := b) (b := a))

theorem zexth_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zexth .and true)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zexth .and true)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zexth .and true)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zexth .and true)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zexth .and true) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zexth) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zexth hType) char_zexth
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun _ a r₂ => Data.RISCV.zexth_and_right (a := r₂) (b := a))
    (fun _ r₁ b => Data.RISCV.zexth_and_left (a := b) (b := r₁))
    (fun h => absurd h (by decide))

theorem zexth_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zexth .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zexth .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zexth .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zexth .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zexth .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zexth) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zexth hType) char_zexth
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zexth_or (a := b) (b := a))

theorem zexth_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .zexth .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .zexth .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .zexth .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .zexth .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .zexth .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.zexth) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_zexth hType) char_zexth
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.zexth_xor (a := b) (b := a))

theorem sextb_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextb .and false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextb .and false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextb .and false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextb .and false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextb .and false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextb) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextb hType) char_sextb
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextb_and (a := b) (b := a))

theorem sextb_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextb .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextb .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextb .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextb .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextb .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextb) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextb hType) char_sextb
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextb_or (a := b) (b := a))

theorem sextb_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sextb .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sextb .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sextb .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sextb .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sextb .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sextb) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sextb hType) char_sextb
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sextb_xor (a := b) (b := a))

theorem sexth_and_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sexth .and false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sexth .and false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sexth .and false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sexth .and false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sexth .and false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sexth) (fdst := fun r₁ r₂ => Data.RISCV.and r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sexth hType) char_sexth
    (fun hType => OperationPtr.Pure.riscv_and hType) char_and
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sexth_and (a := b) (b := a))

theorem sexth_or_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sexth .or false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sexth .or false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sexth .or false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sexth .or false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sexth .or false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sexth) (fdst := fun r₁ r₂ => Data.RISCV.or r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sexth hType) char_sexth
    (fun hType => OperationPtr.Pure.riscv_or hType) char_or
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sexth_or (a := b) (b := a))

theorem sexth_xor_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_of_bitwise_local .sexth .xor false)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_of_bitwise_local .sexth .xor false)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_of_bitwise_local .sexth .xor false)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_of_bitwise_local .sexth .xor false)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_of_bitwise_local .sexth .xor false) h h₂ h₃ h₄ :=
  drop_ext_of_bitwise_local_preservesSemantics
    (fext := Data.RISCV.sexth) (fdst := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
    (fun hType => OperationPtr.Pure.riscv_sexth hType) char_sexth
    (fun hType => OperationPtr.Pure.riscv_xor hType) char_xor
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ a b => Data.RISCV.sexth_xor (a := b) (b := a))

/-! ## `drop_slli_srli_*`:  `srli 63 (slli 63 b) -> b` when `b` is a boolean op

  `op` is a `riscv.srli 63` whose operand is defined by a `riscv.slli 63`, whose operand `b` is in
  turn defined by a boolean-producing `riscv` op (`slt`/`sltu`/…) that returns exactly `0` or `1`.
  The `slli 63; srli 63` round trip isolates bit 0 of `b` and moves it straight back, so for such a
  `b` it is the identity: no operation is created, `op`'s result is forwarded to `b`. This is a
  three-level register-DAG walk (`srli -> slli -> bool`); the "bool op returns 0/1" fact is threaded
  as the `hBoolSem` hypothesis and discharged per instantiation. -/

set_option maxHeartbeats 1000000 in
/-- Shared correctness for the `drop_slli_srli_*` family, generic over the boolean opcode `boolDst`
    (of arity `arity`) whose interpretation always yields a single register in `{0, 1}` (`hBoolSem`)
    and is pure (`hBoolPure`). -/
theorem drop_slli_srli_boolLocal_preservesSemantics {boolDst : Riscv} {arity : Nat}
    (hBoolPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv boolDst → opp.Pure c)
    (hBoolSem : ∀ (props : HasDialectOpInfo.propertiesOf boolDst) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' boolDst props rt ops bo mem = some (.ok res) →
        ∃ r, res = (#[.reg r], mem, none) ∧ (r.val = 0#64 ∨ r.val = 1#64))
    {h : LocalRewritePattern.ReturnOps (drop_slli_srli_boolLocal boolDst arity)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_slli_srli_boolLocal boolDst arity)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_slli_srli_boolLocal boolDst arity)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_slli_srli_boolLocal boolDst arity)} :
    LocalRewritePattern.PreservesSemantics (drop_slli_srli_boolLocal boolDst arity) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, drop_slli_srli_boolLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp op (.riscv .srli) 1`.
  have hMatchSome : (matchOp op ctx.raw (.riscv .srli) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv .srli) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, outerImm⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Outer immediate guard: `outerImm.value.value = 63`.
  have hOuterNe : ¬ (outerImm.value.value ≠ 63) := by
    split at hpattern
    · simp at hpattern
    · assumption
  rw [if_neg hOuterNe] at hpattern
  have hOuterVal : outerImm.value.value = 63 := Decidable.not_not.mp hOuterNe
  -- Peel `getDefiningOp operands[0]!`.
  have hDefSlliSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨slliOp, hDefSlli⟩ := Option.isSome_iff_exists.mp hDefSlliSome
  rw [hDefSlli] at hpattern
  simp only [] at hpattern
  -- Peel `matchOp slliOp (.riscv .slli) 1`.
  have hSlliMatchSome : (matchOp slliOp ctx.raw (.riscv .slli) 1).isSome := by
    cases hM : matchOp slliOp ctx.raw (.riscv .slli) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨slliOperands, innerImm⟩, hSlliMatch⟩ := Option.isSome_iff_exists.mp hSlliMatchSome
  rw [hSlliMatch] at hpattern
  simp only [] at hpattern
  -- Inner immediate guard: `innerImm.value.value = 63`.
  have hInnerNe : ¬ (innerImm.value.value ≠ 63) := by
    split at hpattern
    · simp at hpattern
    · assumption
  rw [if_neg hInnerNe] at hpattern
  have hInnerVal : innerImm.value.value = 63 := Decidable.not_not.mp hInnerNe
  -- Peel `getDefiningOp slliOperands[0]!`.
  have hDefBoolSome : (getDefiningOp slliOperands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp slliOperands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨boolOp, hDefBool⟩ := Option.isSome_iff_exists.mp hDefBoolSome
  rw [hDefBool] at hpattern
  simp only [] at hpattern
  -- Peel `matchOp boolOp (.riscv boolDst) arity`.
  have hBoolMatchSome : (matchOp boolOp ctx.raw (.riscv boolDst) arity).isSome := by
    cases hM : matchOp boolOp ctx.raw (.riscv boolDst) arity with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨boolOperands, boolProps⟩, hBoolMatch⟩ := Option.isSome_iff_exists.mp hBoolMatchSome
  rw [hBoolMatch] at hpattern
  simp only [] at hpattern
  -- Read off the pattern outputs: nothing is created; the result forwards to `slliOperands[0]!`.
  obtain ⟨rfl, rfl, rfl⟩ : ctx = newCtx ∧ newOps = #[] ∧ newValues = #[slliOperands[0]!] := by
    simp at hpattern; grind
  -- Structural facts.
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, hOpProps⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hOp0Mem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨hSlliType, hSlliNumOperands, hSlliNumResults, hSlliOperandsEq, hSlliProps⟩ :=
    matchOp_implies hSlliMatch
  have hSlliOperands : slliOp.getOperands! ctx.raw = #[slliOperands[0]!] := by
    have hsz : slliOperands.size = 1 := by
      rw [hSlliOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hSlliNumOperands]
    rw [← hSlliOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hSlliOpMem : slliOperands[0]! ∈ slliOp.getOperands! ctx.raw := by rw [hSlliOperands]; simp
  have hFib : ctx.raw.FieldsInBounds := ctx.wellFormed.inBounds
  have hOp0In : operands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib opInBounds hOp0Mem
  -- Dominance chain: `slliOp` and `boolOp` both strictly dominate `op`.
  have hSlliSDom : slliOp.strictlyDominates op ctx :=
    strictlyDominates_of_getDefiningOp_of_mem_getOperands ctxDom opInBounds hDefSlli hOp0Mem
  obtain ⟨slliPtr, hSlliPtrEq, hSlliOpEq⟩ := getDefiningOp_implies hDefSlli
  have hSlliOpIn : slliOp.InBounds ctx.raw := by
    rw [hSlliOpEq]
    have hh := (ValuePtr.inBounds_opResult slliPtr ctx.raw).mp (hSlliPtrEq ▸ hOp0In)
    unfold OpResultPtr.InBounds at hh; obtain ⟨hh, -⟩ := hh; exact hh
  have hBoolBaseIn : slliOperands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib hSlliOpIn hSlliOpMem
  have hBoolSDomSlli : boolOp.strictlyDominates slliOp ctx :=
    strictlyDominates_of_getDefiningOp_of_mem_getOperands ctxDom hSlliOpIn hDefBool hSlliOpMem
  have hBoolSDom : boolOp.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hBoolSDomSlli hSlliSDom
  -- Unfold the outer `srli`'s interpretation.
  obtain ⟨s, hOp0Val, hMemOuter, hOpResVal, hCfOuter⟩ :=
    matchRiscvUnaryRegImm_interpretOp_unfold (rop := .srli)
      (f := fun s => Data.RISCV.srli
        (BitVec.ofInt 6 (op.getProperties! ctx.raw (.riscv .srli)).value.value) s)
      opInBounds hOpType hNumResults hOperands
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hinterp
  subst hCfOuter
  -- Pin `operands[0]!` to `slli 63 t` and expose the boolean operand `t`.
  obtain ⟨t, hSlliOpVal, hSlliResVal⟩ :=
    riscv_unaryRegImm_getVarBoth_of_EquationLemmaAt (rop := .slli)
      (f := fun t => Data.RISCV.slli
        (BitVec.ofInt 6 (slliOp.getProperties! ctx.raw (.riscv .slli)).value.value) t)
      ctxDom opInBounds stateWf (fun hT => OperationPtr.Pure.riscv_slli hT)
      hDefSlli hSlliMatch
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hOp0Mem
  -- Pin the boolean operand `slliOperands[0]!` to a register in `{0, 1}`.
  obtain ⟨rb, hBoolVal, hBit⟩ :=
    riscv_bool_getVar?_of_EquationLemmaAt (rop := boolDst)
      (P := fun r => r.val = 0#64 ∨ r.val = 1#64)
      opInBounds stateWf hBoolPure hBoolSem hBoolBaseIn hDefBool hBoolMatch hBoolSDom
  -- Collapse the chain: `s = slli 63 t`, `t = rb ∈ {0, 1}`.
  have hs : s = Data.RISCV.slli
      (BitVec.ofInt 6 (slliOp.getProperties! ctx.raw (.riscv .slli)).value.value) t := by
    have := hOp0Val.symm.trans hSlliResVal; simpa using this
  have ht : t = rb := by have := hSlliOpVal.symm.trans hBoolVal; simpa using this
  have hTBit : t.val = 0#64 ∨ t.val = 1#64 := ht ▸ hBit
  -- The two immediates really are `63`.
  have hXo : (op.getProperties! ctx.raw (.riscv .srli)).value.value = 63 := by
    rw [← hOpProps]; exact hOuterVal
  have hXi : (slliOp.getProperties! ctx.raw (.riscv .slli)).value.value = 63 := by
    rw [← hSlliProps]; exact hInnerVal
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hOpResVal] at hsourceValues
  subst sourceValues
  -- Target dominance / freshness of the forwarded value.
  have hTgtDomSlli : slliOperands[0]!.dominatesIp (InsertPoint.before slliOp) ctx :=
    ctxDom.operand_dominates_op hSlliOpIn hSlliOpMem
  have hTgtDom : slliOperands[0]!.dominatesIp (InsertPoint.before op) ctx :=
    ValuePtr.dominatesIp_before_of_strictlyDominates hTgtDomSlli hSlliSDom
  have hTgtNotOp : slliOperands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSlliSDom) slliOperands[0]! hSlliOpMem
  have hTgtVal :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hBoolBaseIn
      hSlliOpVal hTgtDom hTgtDom hTgtNotOp
  refine ⟨state', by
    simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, Interp, pure], by grind, ?_⟩
  refine ⟨#[RuntimeValue.reg t], by simp [hTgtVal, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  -- `.reg (srli 63 (slli 63 t)) ⊒ .reg t`  ⟺  `srli 63 (slli 63 t) = t`.
  simp only [hs, hXo, hXi]
  have h63 : BitVec.ofInt 6 (63 : Int) = (63 : BitVec 6) := by decide
  rw [h63]
  exact Data.RISCV.drop_slli_srli_of_bit hTBit

/-- `riscv.slt` produces exactly `0` or `1`. -/
theorem drop_slli_srli_slt_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .slt 2) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_slt hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 op2 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.slt op2 op1, e1.symm, Data.RISCV.slt_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.sltu` produces exactly `0` or `1`. -/
theorem drop_slli_srli_sltu_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .sltu 2) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_sltu hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 op2 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.sltu op2 op1, e1.symm, Data.RISCV.sltu_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.slti` produces exactly `0` or `1`. -/
theorem drop_slli_srli_slti_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .slti 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_slti hType)
    (fun props _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.slti (BitVec.ofInt 12 props.value.value) op1, e1.symm, Data.RISCV.slti_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.sltiu` produces exactly `0` or `1`. -/
theorem drop_slli_srli_sltiu_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .sltiu 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_sltiu hType)
    (fun props _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.sltiu (BitVec.ofInt 12 props.value.value) op1, e1.symm,
          Data.RISCV.sltiu_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.seqz` produces exactly `0` or `1`. -/
theorem drop_slli_srli_seqz_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .seqz 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_seqz hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.seqz op1, e1.symm, Data.RISCV.seqz_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.snez` produces exactly `0` or `1`. -/
theorem drop_slli_srli_snez_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .snez 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_snez hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.snez op1, e1.symm, Data.RISCV.snez_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.sltz` produces exactly `0` or `1`. -/
theorem drop_slli_srli_sltz_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .sltz 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_sltz hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.sltz op1, e1.symm, Data.RISCV.sltz_bit⟩
      · exact absurd hh (by simp))

/-- `riscv.sgtz` produces exactly `0` or `1`. -/
theorem drop_slli_srli_sgtz_local_preservesSemantics
    {h h₂ h₃ h₄} : LocalRewritePattern.PreservesSemantics
      (drop_slli_srli_boolLocal .sgtz 1) h h₂ h₃ h₄ :=
  drop_slli_srli_boolLocal_preservesSemantics
    (fun hType => OperationPtr.Pure.riscv_sgtz hType)
    (fun _ _ _ _ _ _ hh => by
      simp only [Riscv.interpretOp', pure, Interp] at hh
      split at hh
      · rename_i op1 heq
        injection hh with e1; injection e1 with e1
        exact ⟨Data.RISCV.sgtz op1, e1.symm, Data.RISCV.sgtz_bit⟩
      · exact absurd hh (by simp))

/-! ## `srl_sra_signbit` / `srlw_sraw_signbit`:  `srl (width-1) (sra _ x) -> srl (width-1) x`

  `op` is a `riscv.<srl> (width-1)` whose operand is defined by a `riscv.<sra>`; a fresh
  `riscv.<srl> (width-1) x` is created over the `sra`'s own source `x` and `op`'s result forwards to
  it. The shift-by-`width-1` keeps only the sign bit, which the earlier arithmetic shift already
  preserves, so the `sra` is redundant. Proven per instantiation (`srli`/`srai` at 64, `srliw`/
  `sraiw` at 32); a generic combinator is blocked by the `cast hSrl` on the immediate properties,
  which collapses to the identity only once `srlDst` is concrete. -/

set_option maxHeartbeats 1000000 in
/-- `riscv.srli 63 (riscv.srai _ x) -> riscv.srli 63 x`. -/
theorem srl_sra_signbit_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (srl_sra_signbitLocal .srli rfl .srai 64)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (srl_sra_signbitLocal .srli rfl .srai 64)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (srl_sra_signbitLocal .srli rfl .srai 64)}
    {h₄ : LocalRewritePattern.ReturnValues (srl_sra_signbitLocal .srli rfl .srai 64)} :
    LocalRewritePattern.PreservesSemantics (srl_sra_signbitLocal .srli rfl .srai 64) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, srl_sra_signbitLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp op (.riscv .srli) 1`.
  have hMatchSome : (matchOp op ctx.raw (.riscv .srli) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv .srli) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, outerImm⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Immediate guard: `outerImm.value.value = 63` (the `cast rfl` is the identity here).
  split at hpattern
  · simp at hpattern
  rename_i hGuard
  have hOuterVal : outerImm.value.value = 63 := by
    have hh := Decidable.not_not.mp hGuard
    have hh2 : outerImm.value.value = (64 : Int) - 1 := hh
    omega
  -- Peel `getDefiningOp operands[0]!`.
  have hDefSraSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨sraOp, hDefSra⟩ := Option.isSome_iff_exists.mp hDefSraSome
  rw [hDefSra] at hpattern
  simp only [] at hpattern
  -- Peel `matchOp sraOp (.riscv .srai) 1`.
  have hSraMatchSome : (matchOp sraOp ctx.raw (.riscv .srai) 1).isSome := by
    cases hM : matchOp sraOp ctx.raw (.riscv .srai) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨sraOperands, sraProps⟩, hSraMatch⟩ := Option.isSome_iff_exists.mp hSraMatchSome
  rw [hSraMatch] at hpattern
  simp only [] at hpattern
  -- Structural facts for `op`.
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, hOpProps⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hOp0Mem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨hSraType, hSraNumOperands, hSraNumResults, hSraOperandsEq, hSraProps⟩ :=
    matchOp_implies hSraMatch
  have hSraOperands : sraOp.getOperands! ctx.raw = #[sraOperands[0]!] := by
    have hsz : sraOperands.size = 1 := by
      rw [hSraOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hSraNumOperands]
    rw [← hSraOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hSraOpMem : sraOperands[0]! ∈ sraOp.getOperands! ctx.raw := by rw [hSraOperands]; simp
  have hFib : ctx.raw.FieldsInBounds := ctx.wellFormed.inBounds
  have hOp0In : operands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib opInBounds hOp0Mem
  -- Dominance: `sraOp` strictly dominates `op`; `sraOperands[0]!` dominates before `op`.
  have hSraSDom : sraOp.strictlyDominates op ctx :=
    strictlyDominates_of_getDefiningOp_of_mem_getOperands ctxDom opInBounds hDefSra hOp0Mem
  obtain ⟨sraPtr, hSraPtrEq, hSraOpEq⟩ := getDefiningOp_implies hDefSra
  have hSraOpIn : sraOp.InBounds ctx.raw := by
    rw [hSraOpEq]
    have hh := (ValuePtr.inBounds_opResult sraPtr ctx.raw).mp (hSraPtrEq ▸ hOp0In)
    unfold OpResultPtr.InBounds at hh; obtain ⟨hh, -⟩ := hh; exact hh
  have hxIn : sraOperands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib hSraOpIn hSraOpMem
  have hDomXSra : sraOperands[0]!.dominatesIp (InsertPoint.before sraOp) ctx :=
    ctxDom.operand_dominates_op hSraOpIn hSraOpMem
  have hDomX : sraOperands[0]!.dominatesIp (InsertPoint.before op) ctx :=
    ValuePtr.dominatesIp_before_of_strictlyDominates hDomXSra hSraSDom
  have xNotOp : sraOperands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSraSDom) sraOperands[0]! hSraOpMem
  -- Unfold the outer `srli`'s interpretation.
  obtain ⟨sv, hOp0Val, hMemOuter, hOpResVal, hCfOuter⟩ :=
    matchRiscvUnaryRegImm_interpretOp_unfold (rop := .srli)
      (f := fun sv => Data.RISCV.srli
        (BitVec.ofInt 6 (op.getProperties! ctx.raw (.riscv .srli)).value.value) sv)
      opInBounds hOpType hNumResults hOperands
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hinterp
  subst hCfOuter
  -- Pin `operands[0]!` to `srai k xv` and expose the `srai`'s source `xv`.
  obtain ⟨xv, hSraOpVal, hSraResVal⟩ :=
    riscv_unaryRegImm_getVarBoth_of_EquationLemmaAt (rop := .srai)
      (f := fun xv => Data.RISCV.srai
        (BitVec.ofInt 6 (sraOp.getProperties! ctx.raw (.riscv .srai)).value.value) xv)
      ctxDom opInBounds stateWf (fun hT => OperationPtr.Pure.riscv_srai hT)
      hDefSra hSraMatch
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hOp0Mem
  -- `sv = srai k xv`.
  have hsv : sv = Data.RISCV.srai
      (BitVec.ofInt 6 (sraOp.getProperties! ctx.raw (.riscv .srai)).value.value) xv := by
    have := hOp0Val.symm.trans hSraResVal; simpa using this
  -- The outer immediate is `63`.
  have hXo : (op.getProperties! ctx.raw (.riscv .srli)).value.value = 63 := by
    rw [← hOpProps]; exact hOuterVal
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hOpResVal] at hsourceValues
  subst sourceValues
  -- Peel the single `srli` creation.
  simp only [bind, Option.bind_eq_some_iff] at hpattern
  peelOpCreation! hpattern ctx₁ newOp hNew hDomX hDomX₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .riscv .srli := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[sraOperands[0]!] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.riscv .srli) = outerImm := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(RegisterType.mk : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    exact hT
  -- Read the refined `sraOperands[0]!` in the target state.
  have hXVal' :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hxIn
      hSraOpVal hDomX hDomX₁ xNotOp
  -- Replay the created `srli` forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := state') (inBounds := by grind)
      (rt := RegisterType.mk none) (props := outerImm)
      (res := Data.RISCV.srli (BitVec.ofInt 6 outerImm.value.value) xv)
      (by intro resultTypes blockOperands mem
          simp [Riscv.interpretOp', pure, Interp])
      hNewType hNewProps hNewOperands hNewResTypes hXVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.reg (Data.RISCV.srli (BitVec.ofInt 6 outerImm.value.value) xv)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  -- `.reg (srli 63 (srai k xv)) ⊒ .reg (srli 63 xv)`  ⟺  `srli 63 (srai k xv) = srli 63 xv`.
  have h63 : BitVec.ofInt 6 (63 : Int) = (63 : BitVec 6) := by decide
  simp only [hsv, hXo, hOpProps, h63]
  exact Data.RISCV.srl_sra_signbit

set_option maxHeartbeats 1000000 in
/-- `i32` analogue: `riscv.srliw 31 (riscv.sraiw _ x) -> riscv.srliw 31 x`. The `srliw`/`sraiw` ops
    read only bits 31:0 (via `extractLsb'`/`extractLsb`) and sign-extend; the shift-by-31 keeps only
    bit 31 (the 32-bit sign bit), which the `sraiw` preserves. -/
theorem srlw_sraw_signbit_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (srl_sra_signbitLocal .srliw rfl .sraiw 32)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (srl_sra_signbitLocal .srliw rfl .sraiw 32)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (srl_sra_signbitLocal .srliw rfl .sraiw 32)}
    {h₄ : LocalRewritePattern.ReturnValues (srl_sra_signbitLocal .srliw rfl .sraiw 32)} :
    LocalRewritePattern.PreservesSemantics (srl_sra_signbitLocal .srliw rfl .sraiw 32) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, srl_sra_signbitLocal]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp op (.riscv .srliw) 1`.
  have hMatchSome : (matchOp op ctx.raw (.riscv .srliw) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv .srliw) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, outerImm⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Immediate guard: `outerImm.value.value = 31` (the `cast rfl` is the identity here).
  split at hpattern
  · simp at hpattern
  rename_i hGuard
  have hOuterVal : outerImm.value.value = 31 := by
    have hh := Decidable.not_not.mp hGuard
    have hh2 : outerImm.value.value = (32 : Int) - 1 := hh
    omega
  -- Peel `getDefiningOp operands[0]!`.
  have hDefSraSome : (getDefiningOp operands[0]! ctx.raw).isSome := by
    cases hD : getDefiningOp operands[0]! ctx.raw with
    | some y => rfl
    | none => rw [hD] at hpattern; simp at hpattern
  obtain ⟨sraOp, hDefSra⟩ := Option.isSome_iff_exists.mp hDefSraSome
  rw [hDefSra] at hpattern
  simp only [] at hpattern
  -- Peel `matchOp sraOp (.riscv .sraiw) 1`.
  have hSraMatchSome : (matchOp sraOp ctx.raw (.riscv .sraiw) 1).isSome := by
    cases hM : matchOp sraOp ctx.raw (.riscv .sraiw) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨sraOperands, sraProps⟩, hSraMatch⟩ := Option.isSome_iff_exists.mp hSraMatchSome
  rw [hSraMatch] at hpattern
  simp only [] at hpattern
  -- Structural facts for `op`.
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, hOpProps⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hOp0Mem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨hSraType, hSraNumOperands, hSraNumResults, hSraOperandsEq, hSraProps⟩ :=
    matchOp_implies hSraMatch
  have hSraOperands : sraOp.getOperands! ctx.raw = #[sraOperands[0]!] := by
    have hsz : sraOperands.size = 1 := by
      rw [hSraOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hSraNumOperands]
    rw [← hSraOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hSraOpMem : sraOperands[0]! ∈ sraOp.getOperands! ctx.raw := by rw [hSraOperands]; simp
  have hFib : ctx.raw.FieldsInBounds := ctx.wellFormed.inBounds
  have hOp0In : operands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib opInBounds hOp0Mem
  -- Dominance: `sraOp` strictly dominates `op`; `sraOperands[0]!` dominates before `op`.
  have hSraSDom : sraOp.strictlyDominates op ctx :=
    strictlyDominates_of_getDefiningOp_of_mem_getOperands ctxDom opInBounds hDefSra hOp0Mem
  obtain ⟨sraPtr, hSraPtrEq, hSraOpEq⟩ := getDefiningOp_implies hDefSra
  have hSraOpIn : sraOp.InBounds ctx.raw := by
    rw [hSraOpEq]
    have hh := (ValuePtr.inBounds_opResult sraPtr ctx.raw).mp (hSraPtrEq ▸ hOp0In)
    unfold OpResultPtr.InBounds at hh; obtain ⟨hh, -⟩ := hh; exact hh
  have hxIn : sraOperands[0]!.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds hFib hSraOpIn hSraOpMem
  have hDomXSra : sraOperands[0]!.dominatesIp (InsertPoint.before sraOp) ctx :=
    ctxDom.operand_dominates_op hSraOpIn hSraOpMem
  have hDomX : sraOperands[0]!.dominatesIp (InsertPoint.before op) ctx :=
    ValuePtr.dominatesIp_before_of_strictlyDominates hDomXSra hSraSDom
  have xNotOp : sraOperands[0]! ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hSraSDom) sraOperands[0]! hSraOpMem
  -- Unfold the outer `srliw`'s interpretation.
  obtain ⟨sv, hOp0Val, hMemOuter, hOpResVal, hCfOuter⟩ :=
    matchRiscvUnaryRegImm_interpretOp_unfold (rop := .srliw)
      (f := fun sv => Data.RISCV.srliw
        (BitVec.ofInt 5 (op.getProperties! ctx.raw (.riscv .srliw)).value.value) sv)
      opInBounds hOpType hNumResults hOperands
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hinterp
  subst hCfOuter
  -- Pin `operands[0]!` to `sraiw k xv` and expose the `sraiw`'s source `xv`.
  obtain ⟨xv, hSraOpVal, hSraResVal⟩ :=
    riscv_unaryRegImm_getVarBoth_of_EquationLemmaAt (rop := .sraiw)
      (f := fun xv => Data.RISCV.sraiw
        (BitVec.ofInt 5 (sraOp.getProperties! ctx.raw (.riscv .sraiw)).value.value) xv)
      ctxDom opInBounds stateWf (fun hT => OperationPtr.Pure.riscv_sraiw hT)
      hDefSra hSraMatch
      (by intro rt ops bo mem res hh
          simp only [Riscv.interpretOp', pure, Interp] at hh
          split at hh
          · rename_i op1 heq
            refine ⟨op1, Array.toList_inj.mp heq, ?_⟩
            injection hh with e1; injection e1 with e1; exact e1.symm
          · exact absurd hh (by simp))
      hOp0Mem
  -- `sv = sraiw k xv`.
  have hsv : sv = Data.RISCV.sraiw
      (BitVec.ofInt 5 (sraOp.getProperties! ctx.raw (.riscv .sraiw)).value.value) xv := by
    have := hOp0Val.symm.trans hSraResVal; simpa using this
  -- The outer immediate is `31`.
  have hXo : (op.getProperties! ctx.raw (.riscv .srliw)).value.value = 31 := by
    rw [← hOpProps]; exact hOuterVal
  -- Source value.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hOpResVal] at hsourceValues
  subst sourceValues
  -- Peel the single `srliw` creation.
  simp only [bind, Option.bind_eq_some_iff] at hpattern
  peelOpCreation! hpattern ctx₁ newOp hNew hDomX hDomX₁
  cleanupHpattern hpattern
  have hNewType : newOp.getOpType! ctx₁.raw = .riscv .srliw := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[sraOperands[0]!] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewProps : newOp.getProperties! ctx₁.raw (.riscv .srliw) = outerImm := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNew (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw
      = #[(RegisterType.mk : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hNew (operation := newOp)
    rw [if_pos rfl] at hT
    exact hT
  -- Read the refined `sraOperands[0]!` in the target state.
  have hXVal' :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hxIn
      hSraOpVal hDomX hDomX₁ xNotOp
  -- Replay the created `srliw` forward.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := state') (inBounds := by grind)
      (rt := RegisterType.mk none) (props := outerImm)
      (res := Data.RISCV.srliw (BitVec.ofInt 5 outerImm.value.value) xv)
      (by intro resultTypes blockOperands mem
          simp [Riscv.interpretOp', pure, Interp])
      hNewType hNewProps hNewOperands hNewResTypes hXVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.reg (Data.RISCV.srliw (BitVec.ofInt 5 outerImm.value.value) xv)],
    by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  -- `.reg (srliw 31 (sraiw k xv)) ⊒ .reg (srliw 31 xv)`  ⟺  `srliw 31 (sraiw k xv) = srliw 31 xv`.
  have h31 : BitVec.ofInt 5 (31 : Int) = (31 : BitVec 5) := by decide
  simp only [hsv, hXo, hOpProps, h31]
  exact Data.RISCV.srlw_sraw_signbit

/-! ## RISC-V-dialect low-word extension drops feeding a consumer that reads only bits 31:0

  `riscv.<dst> (riscv.<ext> x) -> riscv.<dst> x` (unary immediate `dst`) and the binary analogue.
  Since `Data.RISCV.Reg` is total (no poison), refinement on `RuntimeValue.reg` is equality, so the
  data obligation is the ordinary low-word equality `dstFn (extFn x) = dstFn x` (proven in
  `Veir/Passes/RISCVCombines/Proofs.lean`). One op is created (the `dst` with its extension operand(s)
  stripped) and the matched op's result is forwarded to it. -/

/-- Props-threaded analogue of `matchRiscvUnaryReg_interpretOp_unfold`: unfold one successful
    interpretation of a unary reg-to-reg `riscv` op `rop` carrying the fixed property bundle `props`
    (typically an immediate). The result function `g` may depend on `props`. -/
theorem matchRiscvUnaryRegProps_interpretOp_unfold {rop : Riscv} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {operand : ValuePtr} {g : Data.RISCV.Reg → Data.RISCV.Reg}
    {props : HasDialectOpInfo.propertiesOf rop}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .riscv rop)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hProps : op.getProperties! ctx.raw (.riscv rop) = props)
    (hSem : ∀ (rt : Array TypeAttr) (ops : Array RuntimeValue) (bo : Array BlockPtr)
        (mem : MemoryState) (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (g r)], mem, none))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ r, state.variables.getVar? operand = some (RuntimeValue.reg r) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.reg (g r)) ∧
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
  have hOperand0 : op.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[val] := by
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
  simp only [interpretOp'] at hInterp'
  rw [hProps] at hInterp'
  obtain ⟨r, hopsEq, hresEq⟩ := hSem _ _ _ _ _ hInterp'
  obtain rfl : val = RuntimeValue.reg r := by simpa using hopsEq
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.reg (g r)] ∧
      mem' = state.memory ∧ cf = none := by simpa using hresEq
  subst hNew
  refine ⟨r, hgetVar, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- When `stripDefiningExt ext v ctx` reports a change, `v` is defined by a `riscv.<ext>` op and the
    returned value is that op's (single) operand. -/
theorem stripDefiningExt_eq_some {ext : Riscv} {v src : ValuePtr} {ctx : IRContext OpCode}
    (h : stripDefiningExt ext v ctx = (src, true)) :
    ∃ (innerOp : OperationPtr) (iOperands : Array ValuePtr)
      (iProps : HasOpInfo.propertiesOf (OpCode.riscv ext)),
      getDefiningOp v ctx = some innerOp ∧
      matchOp innerOp ctx (.riscv ext) 1 = some (iOperands, iProps) ∧ src = iOperands[0]! := by
  cases hd : getDefiningOp v ctx with
  | none => simp [stripDefiningExt, hd] at h
  | some innerOp =>
    cases hm : matchOp innerOp ctx (.riscv ext) 1 with
    | none => simp [stripDefiningExt, hd, hm] at h
    | some pr =>
      obtain ⟨iOperands, iProps⟩ := pr
      refine ⟨innerOp, iOperands, iProps, rfl, hm, ?_⟩
      simp only [stripDefiningExt, hd, hm] at h
      injection h with h1 h2
      exact h1.symm

set_option maxHeartbeats 1000000 in
/-- Ext-strip reader: a value `base` that is an operand of `op` and is defined by a unary
    reg-to-reg `riscv` op `rop` (whose data action is `extFn`, characterised by `hSem`) reads, in a
    source state satisfying `EquationLemmaAt` before `op`, as `.reg (extFn r)` for a register `r`
    that is also the value of the extension's own operand `iOperands[0]!` — and that operand
    dominates the point before `op` and is not a result of `op`. This is what a low-word combine
    needs to replay the `dst` op with the extension stripped. -/
theorem riscv_unaryReg_stripExt_getVar? {rop : Riscv}
    {extFn : Data.RISCV.Reg → Data.RISCV.Reg} {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (_ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv rop → opp.Pure c)
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (extFn r)], mem, none))
    {base : ValuePtr} {innerOp : OperationPtr} {iOperands : Array ValuePtr}
    {iProps : HasOpInfo.propertiesOf (OpCode.riscv rop)}
    (hDef : getDefiningOp base ctx.raw = some innerOp)
    (hMatch : matchOp innerOp ctx.raw (.riscv rop) 1 = some (iOperands, iProps))
    (hOperand : base ∈ op.getOperands! ctx.raw) :
    ∃ r : Data.RISCV.Reg,
      state.variables.getVar? (iOperands[0]!) = some (RuntimeValue.reg r) ∧
      state.variables.getVar? base = some (RuntimeValue.reg (extFn r)) ∧
      (iOperands[0]!).dominatesIp (InsertPoint.before op) ctx ∧
      (iOperands[0]!) ∉ op.getResults! ctx.raw ∧
      (iOperands[0]!).InBounds ctx.raw := by
  obtain ⟨basePtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hInnerType, hInnerNumOperands, hInnerNumResults, hInnerOperandsEq, -⟩ :=
    matchOp_implies hMatch
  have hInnerSingleton :
      basePtr.op.getOperands! ctx.raw = #[(basePtr.op.getOperands! ctx.raw)[0]!] := by
    have hsz : (basePtr.op.getOperands! ctx.raw).size = 1 := by
      rw [OperationPtr.getOperands!.size_eq_getNumOperands!, hInnerNumOperands]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hInnerOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hbaseIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hbaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hInnerDefines : (ValuePtr.opResult basePtr).getDefiningOp! ctx.raw = some basePtr.op := by
    have hOwner := (ctx.wellFormed.operations basePtr.op hInnerOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hInnerSDom : basePtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hInnerDefines hOperand
  have hInnerDomIp : basePtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hInnerPure : basePtr.op.Pure ctx.raw := hPure hInnerType
  obtain ⟨cfI, hInterpInner⟩ := stateWf basePtr.op hInnerOpIn hInnerPure hInnerDomIp
  obtain ⟨r, hOperandVal, -, hResVal, -⟩ :=
    matchRiscvUnaryReg_interpretOp_unfold (rop := rop) (f := extFn) hInnerOpIn hInnerType
      hInnerNumResults hInnerSingleton hSem hInterpInner
  -- `iOperands[0]! = (basePtr.op.getOperands!)[0]!`.
  have hSrcEq : iOperands[0]! = (basePtr.op.getOperands! ctx.raw)[0]! := by rw [hInnerOperandsEq]
  have hSrcMem : (basePtr.op.getOperands! ctx.raw)[0]! ∈ basePtr.op.getOperands! ctx.raw := by
    rw [hInnerSingleton]; simp
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSrcEq]; exact hOperandVal
  · rw [hbaseEq]; exact hResVal
  · rw [hSrcEq]
    exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hInnerOpIn hSrcMem) hInnerSDom
  · rw [hSrcEq]
    exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hInnerSDom) _ hSrcMem
  · have hGetOperand : basePtr.op.getOperand! ctx.raw 0 = (basePtr.op.getOperands! ctx.raw)[0]! := by
      grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
    rw [hSrcEq, ← hGetOperand]; grind

set_option maxHeartbeats 1000000 in
/-- Shared correctness for `riscv.<dst> (riscv.<ext> x) -> riscv.<dst> x`, over any unary
    immediate reg-to-reg consumer `dst` (data action `dstFn`, depending on its property bundle) that
    reads only bits 31:0 of its operand, and any width extension `ext` (data action `extFn`) that
    leaves bits 31:0 unchanged. The soundness fact is the low-word equality `hLowWord`. One `dst` op
    is created with the extension stripped; the matched op's result forwards to it. Registers carry
    no poison, so `hLowWord` (a plain equality) discharges the refinement exactly. -/
theorem drop_ext_unary_imm_low_word_local_preservesSemantics {ext dst : Riscv}
    {extFn : Data.RISCV.Reg → Data.RISCV.Reg}
    {dstFn : HasDialectOpInfo.propertiesOf dst → Data.RISCV.Reg → Data.RISCV.Reg}
    (hExtPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv ext → opp.Pure c)
    (hExtSem : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (extFn r)], mem, none))
    (hDstChar : ∀ (props : HasDialectOpInfo.propertiesOf dst) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' dst props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (dstFn props r)], mem, none))
    (hDstFwd : ∀ (props : HasDialectOpInfo.propertiesOf dst) (r : Data.RISCV.Reg)
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst props rt #[.reg r] bo mem
          = some (.ok (#[.reg (dstFn props r)], mem, none)))
    (hLowWord : ∀ (props : HasDialectOpInfo.propertiesOf dst) (r : Data.RISCV.Reg),
        dstFn props (extFn r) = dstFn props r)
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local ext dst)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local ext dst)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local ext dst)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local ext dst)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local ext dst) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, drop_ext_unary_imm_low_word_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp dst`.
  have hMatchSome : (matchOp op ctx.raw (.riscv dst) 1).isSome := by
    cases hM : matchOp op ctx.raw (.riscv dst) 1 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, oProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, hPropsEq⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!] := by
    have hsz : operands.size = 1 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      obtain rfl : i = 0 := by omega
      simp [getElem!_pos, hsz]
  -- Peel `stripDefiningExt` and the `if !changed` guard.
  rcases hstrip : stripDefiningExt ext operands[0]! ctx.raw with ⟨src, changed⟩
  rw [hstrip] at hpattern
  simp only [] at hpattern
  split at hpattern
  · simp at hpattern
  rename_i hcond
  obtain rfl : changed = true := by cases changed with | true => rfl | false => exact (hcond rfl).elim
  obtain ⟨innerOp, extOperands, extProps, hDef, hExtMatch, rfl⟩ := stripDefiningExt_eq_some hstrip
  -- Read the stripped operand `src = extOperands[0]!` and the ext result value.
  have hOperandMem : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨w, hSrcVal, hBaseVal, hDomSrc, hSrcNotOp, hSrcIn⟩ :=
    riscv_unaryReg_stripExt_getVar? (rop := ext) (extFn := extFn) ctxDom ctxVerif opInBounds
      stateWf hExtPure hExtSem hDef hExtMatch hOperandMem
  -- Unfold the matched `dst` op's interpretation (its operand value is `.reg (extFn w)`).
  obtain ⟨a, hOpndVal, hMemEq, hResVal, hCf⟩ :=
    matchRiscvUnaryRegProps_interpretOp_unfold (rop := dst) (g := dstFn oProps) (props := oProps)
      opInBounds hOpType hNumResults hOperands hPropsEq.symm
      (fun rt ops bo mem res hh => hDstChar oProps rt ops bo mem res hh) hinterp
  subst hCf
  obtain rfl : a = extFn w := by
    have := hOpndVal.symm.trans hBaseVal; simpa using this
  -- Source value: the single result `.reg (dstFn oProps (extFn w))`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the single op-creation and transport `src`'s dominance to the new context.
  simp only [bind, Option.bind_eq_some_iff] at hpattern
  peelOpCreation! hpattern ctx₁ newOp hNewCtx hDomSrc hDomSrc₁
  obtain ⟨rfl, rfl, rfl⟩ :
      ctx₁ = newCtx ∧ newOps = #[newOp] ∧
        newValues = #[ValuePtr.opResult (newOp.getResult 0)] := by
    simp at hpattern; grind
  -- Read `src`'s refined value in the target state (register refinement is equality).
  have hSrcVal' :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hSrcIn hSrcVal
      hDomSrc hDomSrc₁ hSrcNotOp
  -- Structural facts about the created `dst` op.
  have hNewType : newOp.getOpType! ctx₁.raw = .riscv dst := by grind
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[extOperands[0]!] := by grind
  have hNewProps : newOp.getProperties! ctx₁.raw (.riscv dst) = oProps := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hNewCtx (operation := newOp)]
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hNewCtx (operation := newOp)]
  -- Replay the created `dst` op in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := state') (inBounds := by grind)
      (res := dstFn oProps w) (props := oProps)
      (fun rt bo mem => hDstFwd oProps w rt bo mem)
      hNewType hNewProps hNewOperands hNewResTypes hSrcVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.reg (dstFn oProps w)], by simp [hRes₁, Option.bind, Option.map], ?_⟩
  exact RuntimeValue.arrayIsRefinedBy_singleton.mpr (hLowWord oProps w)

/-- Shared `hExtSem` discharge for a zero/sign width extension viewed as the *stripped* op: a
    successful `riscv.<ext>` run reads one register `r` and returns `.reg (extFn r)`. -/
private theorem riscv_ext_char {ext : Riscv} {extFn : Data.RISCV.Reg → Data.RISCV.Reg}
    (hfwd : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (r : Data.RISCV.Reg) (bo : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' ext props rt #[.reg r] bo mem
          = some (.ok (#[.reg (extFn r)], mem, none)))
    (hshape : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r]) :
    ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
      (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
      (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
      Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
      ∃ r, ops = #[.reg r] ∧ res = (#[.reg (extFn r)], mem, none) := by
  intro props rt ops bo mem res h
  obtain ⟨r, rfl⟩ := hshape props rt ops bo mem res h
  rw [hfwd props rt r bo mem] at h
  exact ⟨r, rfl, by injection h with h; injection h with h; exact h.symm⟩

/-! ### `drop_ext_unary_imm_low_word` instantiations (8 registered patterns) -/

theorem drop_zextw_addiw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .zextw .addiw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .zextw .addiw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .zextw .addiw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .zextw .addiw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .zextw .addiw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .zextw) (dst := .addiw)
    (extFn := Data.RISCV.zextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.addiw (BitVec.ofInt 12 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (riscv_ext_char (extFn := Data.RISCV.zextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_zextw_addiw)


theorem drop_zextw_roriw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .zextw .roriw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .zextw .roriw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .zextw .roriw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .zextw .roriw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .zextw .roriw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .zextw) (dst := .roriw)
    (extFn := Data.RISCV.zextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.roriw (BitVec.ofInt 5 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (riscv_ext_char (extFn := Data.RISCV.zextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_zextw_roriw)


theorem drop_zextw_srliw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .zextw .srliw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .zextw .srliw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .zextw .srliw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .zextw .srliw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .zextw .srliw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .zextw) (dst := .srliw)
    (extFn := Data.RISCV.zextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.srliw (BitVec.ofInt 5 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (riscv_ext_char (extFn := Data.RISCV.zextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_zextw_srliw)


theorem drop_zextw_sextw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .zextw .sextw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .zextw .sextw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .zextw .sextw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .zextw .sextw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .zextw .sextw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .zextw) (dst := .sextw)
    (extFn := Data.RISCV.zextw)
    (dstFn := fun (_ : Unit) r => Data.RISCV.sextw r)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (riscv_ext_char (extFn := Data.RISCV.zextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_zextw_sextw)


theorem drop_sextw_addiw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .sextw .addiw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .sextw .addiw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .sextw .addiw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .sextw .addiw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .sextw .addiw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .sextw) (dst := .addiw)
    (extFn := Data.RISCV.sextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.addiw (BitVec.ofInt 12 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (riscv_ext_char (extFn := Data.RISCV.sextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_sextw_addiw)


theorem drop_sextw_roriw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .sextw .roriw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .sextw .roriw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .sextw .roriw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .sextw .roriw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .sextw .roriw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .sextw) (dst := .roriw)
    (extFn := Data.RISCV.sextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.roriw (BitVec.ofInt 5 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (riscv_ext_char (extFn := Data.RISCV.sextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_sextw_roriw)


theorem drop_sextw_srliw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .sextw .srliw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .sextw .srliw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .sextw .srliw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .sextw .srliw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .sextw .srliw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .sextw) (dst := .srliw)
    (extFn := Data.RISCV.sextw)
    (dstFn := fun (props : RISCVImmediateProperties) r =>
      Data.RISCV.srliw (BitVec.ofInt 5 props.value.value) r)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (riscv_ext_char (extFn := Data.RISCV.sextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_sextw_srliw)


theorem drop_sextw_zextw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_unary_imm_low_word_local .sextw .zextw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_unary_imm_low_word_local .sextw .zextw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_unary_imm_low_word_local .sextw .zextw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_unary_imm_low_word_local .sextw .zextw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_unary_imm_low_word_local .sextw .zextw)
      h h₂ h₃ h₄ :=
  drop_ext_unary_imm_low_word_local_preservesSemantics (ext := .sextw) (dst := .zextw)
    (extFn := Data.RISCV.sextw)
    (dstFn := fun (_ : Unit) r => Data.RISCV.zextw r)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (riscv_ext_char (extFn := Data.RISCV.sextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (fun _ _ _ _ _ _ h => by
      simp only [Riscv.interpretOp', pure, Interp] at h
      split at h
      · rename_i r heq
        exact ⟨r, Array.toList_inj.mp heq, by injection h with h; injection h with h; exact h.symm⟩
      · exact absurd h (by simp))
    (fun _ r _ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun _ _ => Data.RISCV.drop_sextw_zextw)


/-! ### `drop_ext_binary_low_word` (backs `drop_zextw_addw`, `drop_sextw_addw`) -/

/-- Binary analogue of `matchRiscvUnaryReg_interpretOp_unfold`: unfold one successful interpretation
    of a binary reg-to-reg `riscv` op `rop` whose action is `f` (fully characterised by `hSem`). -/
theorem matchRiscvBinaryReg_interpretOp_unfold {rop : Riscv} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {o0 o1 : ValuePtr} {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .riscv rop)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[o0, o1])
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) →
        ∃ r₀ r₁, ops = #[.reg r₀, .reg r₁] ∧ res = (#[.reg (f r₀ r₁)], mem, none))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf))) :
    ∃ r₀ r₁, state.variables.getVar? o0 = some (RuntimeValue.reg r₀) ∧
      state.variables.getVar? o1 = some (RuntimeValue.reg r₁) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.reg (f r₀ r₁)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hO0Eq : o0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hO1Eq : o1 = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨v0, hv0⟩ := Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨v1, hv1⟩ := Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hg0 : state.variables.getVar? o0 = some v0 := by
    rw [hO0Eq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hv0
  have hg1 : state.variables.getVar? o1 = some v1 := by
    rw [hO1Eq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hv1
  have hOperand0 : op.getOperand! ctx.raw 0 = o0 := by
    rw [hO0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = o1 := by
    rw [hO1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op = some #[v0, v1] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hg0
    | 1, _ => simpa [hOperand1] using hg1
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp'] at hInterp'
  obtain ⟨r₀, r₁, hopsEq, hresEq⟩ := hSem _ _ _ _ _ _ hInterp'
  obtain ⟨rfl, rfl⟩ : v0 = RuntimeValue.reg r₀ ∧ v1 = RuntimeValue.reg r₁ := by
    simpa using hopsEq
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[RuntimeValue.reg (f r₀ r₁)] ∧
      mem' = state.memory ∧ cf = none := by simpa using hresEq
  subst hNew
  refine ⟨r₀, r₁, hg0, hg1, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- When `stripDefiningExt` reports *no* change, the returned value is the input unchanged. -/
theorem stripDefiningExt_eq_false {ext : Riscv} {v s : ValuePtr} {ctx : IRContext OpCode}
    (h : stripDefiningExt ext v ctx = (s, false)) : s = v := by
  cases hd : getDefiningOp v ctx with
  | none => simp only [stripDefiningExt, hd] at h; injection h with h1 _; exact h1.symm
  | some innerOp =>
    cases hm : matchOp innerOp ctx (.riscv ext) 1 with
    | none => simp only [stripDefiningExt, hd, hm] at h; injection h with h1 _; exact h1.symm
    | some pr =>
      obtain ⟨iOperands, iProps⟩ := pr
      simp only [stripDefiningExt, hd, hm] at h; injection h with _ h2; exact absurd h2 (by simp)

/-- Unified reader for a `stripDefiningExt` result: whether or not the extension was stripped, the
    returned value `s` reads as some register `sval` (equal to the *original* operand value when
    unchanged, or the pre-extension value when stripped), dominates the point before `op`, is not a
    result of `op`, and is in bounds. -/
theorem stripDefiningExt_getVar? {rop : Riscv} {extFn : Data.RISCV.Reg → Data.RISCV.Reg}
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    (hPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv rop → opp.Pure c)
    (hSem : ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (extFn r)], mem, none))
    {v s : ValuePtr} {changed : Bool} {vval : Data.RISCV.Reg}
    (hstrip : stripDefiningExt rop v ctx.raw = (s, changed))
    (hv : v ∈ op.getOperands! ctx.raw)
    (hvVal : state.variables.getVar? v = some (RuntimeValue.reg vval)) :
    ∃ sval, state.variables.getVar? s = some (RuntimeValue.reg sval) ∧
      vval = (if changed then extFn sval else sval) ∧
      s.dominatesIp (InsertPoint.before op) ctx ∧
      s ∉ op.getResults! ctx.raw ∧ s.InBounds ctx.raw := by
  cases changed with
  | false =>
    obtain rfl := stripDefiningExt_eq_false hstrip
    refine ⟨vval, hvVal, by simp, ?_, ?_, ?_⟩
    · exact ctxDom.operand_dominates_op opInBounds hv
    · grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
    · grind [WfIRContext.Dom.operand_dominates_op]
  | true =>
    obtain ⟨innerOp, extOperands, extProps, hDef, hExtMatch, rfl⟩ := stripDefiningExt_eq_some hstrip
    obtain ⟨sval, hSrcVal, hBaseVal, hDomSrc, hSrcNotOp, hSrcIn⟩ :=
      riscv_unaryReg_stripExt_getVar? (rop := rop) (extFn := extFn) ctxDom ctxVerif opInBounds
        stateWf hPure hSem hDef hExtMatch hv
    refine ⟨sval, hSrcVal, ?_, hDomSrc, hSrcNotOp, hSrcIn⟩
    have := hvVal.symm.trans hBaseVal
    simp only [if_true]; simpa using this

set_option maxHeartbeats 1000000 in
/-- Shared correctness for `riscv.<dst> (riscv.<ext> x) y -> riscv.<dst> x y` (and symmetrically on
    the second operand), over any binary reg-to-reg consumer `dst` (action `dstFn`) that reads only
    bits 31:0 of *each* operand, and any extension `ext` (action `extFn`) leaving bits 31:0
    unchanged. Either operand (or both) may carry the stripped extension; the soundness facts are the
    per-operand low-word equalities `hLowL`/`hLowR`. -/
theorem drop_ext_binary_low_word_local_preservesSemantics {ext dst : Riscv}
    {extFn : Data.RISCV.Reg → Data.RISCV.Reg}
    {dstFn : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hExtPure : ∀ {opp : OperationPtr} {c : IRContext OpCode},
        opp.getOpType! c = .riscv ext → opp.Pure c)
    (hExtSem : ∀ (props : HasDialectOpInfo.propertiesOf ext) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' ext props rt ops bo mem = some (.ok res) →
        ∃ r, ops = #[.reg r] ∧ res = (#[.reg (extFn r)], mem, none))
    (hDstChar : ∀ (props : HasDialectOpInfo.propertiesOf dst) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' dst props rt ops bo mem = some (.ok res) →
        ∃ r₀ r₁, ops = #[.reg r₀, .reg r₁] ∧ res = (#[.reg (dstFn r₀ r₁)], mem, none))
    (hDstFwd : ∀ (props : HasDialectOpInfo.propertiesOf dst) (r₀ r₁ : Data.RISCV.Reg)
        (rt : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' dst props rt #[.reg r₀, .reg r₁] bo mem
          = some (.ok (#[.reg (dstFn r₀ r₁)], mem, none)))
    (hLowL : ∀ a b, dstFn (extFn a) b = dstFn a b)
    (hLowR : ∀ a b, dstFn a (extFn b) = dstFn a b)
    {h : LocalRewritePattern.ReturnOps (drop_ext_binary_low_word_local ext dst)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_binary_low_word_local ext dst)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_binary_low_word_local ext dst)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_binary_low_word_local ext dst)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_binary_low_word_local ext dst) h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, drop_ext_binary_low_word_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp only [pure] at hpattern
  -- Peel the outer `matchOp dst` (two operands).
  have hMatchSome : (matchOp op ctx.raw (.riscv dst) 2).isSome := by
    cases hM : matchOp op ctx.raw (.riscv dst) 2 with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨operands, oProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumOperands, hNumResults, hOperandsEq, hPropsEq⟩ := matchOp_implies hMatch
  have hOperands : op.getOperands! ctx.raw = #[operands[0]!, operands[1]!] := by
    have hsz : operands.size = 2 := by
      rw [hOperandsEq, OperationPtr.getOperands!.size_eq_getNumOperands!, hNumOperands]
    rw [← hOperandsEq]
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      have hi2 : i < 2 := by simpa using h2
      match i, hi2 with
      | 0, _ => simp [getElem!_pos, hsz]
      | 1, _ => simp [getElem!_pos, hsz]
  -- Peel both `stripDefiningExt`s and the `if !lhsChanged && !rhsChanged` guard.
  rcases hstripL : stripDefiningExt ext operands[0]! ctx.raw with ⟨lhs, lhsChanged⟩
  rcases hstripR : stripDefiningExt ext operands[1]! ctx.raw with ⟨rhs, rhsChanged⟩
  rw [hstripL, hstripR] at hpattern
  simp only [] at hpattern
  split at hpattern
  · simp at hpattern
  -- Unfold the matched binary `dst` op's interpretation.
  obtain ⟨r₀, r₁, hO0Val, hO1Val, hMemEq, hResVal, hCf⟩ :=
    matchRiscvBinaryReg_interpretOp_unfold (rop := dst) (f := dstFn) opInBounds hOpType hNumResults
      hOperands (fun props rt ops bo mem res hh => hDstChar props rt ops bo mem res hh) hinterp
  subst hCf
  -- Read both stripped operands.
  have hMem0 : operands[0]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  have hMem1 : operands[1]! ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  obtain ⟨lval, hLVal, hLEq, hDomL, hLNotOp, hLIn⟩ :=
    stripDefiningExt_getVar? (rop := ext) (extFn := extFn) ctxDom ctxVerif opInBounds stateWf
      hExtPure hExtSem hstripL hMem0 hO0Val
  obtain ⟨rval, hRVal, hREq, hDomR, hRNotOp, hRIn⟩ :=
    stripDefiningExt_getVar? (rop := ext) (extFn := extFn) ctxDom ctxVerif opInBounds stateWf
      hExtPure hExtSem hstripR hMem1 hO1Val
  -- Source value: `.reg (dstFn r₀ r₁)`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the single op-creation and transport both dominances.
  simp only [bind, Option.bind_eq_some_iff] at hpattern
  peelOpCreation!₂ hpattern ctx₁ newOp hNewCtx hDomL hDomL₁ hDomR hDomR₁
  obtain ⟨rfl, rfl, rfl⟩ :
      ctx₁ = newCtx ∧ newOps = #[newOp] ∧
        newValues = #[ValuePtr.opResult (newOp.getResult 0)] := by
    simp at hpattern; grind
  -- Read both operands' refined values in the target state.
  have hLVal' :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hLIn hLVal
      hDomL hDomL₁ hLNotOp
  have hRVal' :=
    LocalRewritePattern.exists_refined_reg_getVar? valueRefinement state'Dom hRIn hRVal
      hDomR hDomR₁ hRNotOp
  -- Structural facts about the created `dst` op.
  have hNewType : newOp.getOpType! ctx₁.raw = .riscv dst := by grind
  have hNewOperands : newOp.getOperands! ctx₁.raw = #[lhs, rhs] := by grind
  have hNewResTypes : newOp.getResultTypes! ctx₁.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hNewCtx (operation := newOp)]
  -- Replay the created binary `dst` op in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := state') (inBounds := by grind)
      (r₁ := lval) (r₂ := rval) (f := dstFn)
      (fun props rt bo mem => hDstFwd props lval rval rt bo mem)
      hNewType hNewOperands hNewResTypes hLVal' hRVal'
  refine ⟨s₁, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.reg (dstFn lval rval)], by simp [hRes₁, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ?_
  -- `dstFn r₀ r₁ = dstFn lval rval` since stripping only rewrites bits `dstFn` ignores.
  rw [hLEq, hREq]
  cases lhsChanged <;> cases rhsChanged <;> simp [hLowL, hLowR]

/-- Binary analogue of `riscv_ext_char`: build the full characterisation of a binary reg op from its
    forward evaluation `hfwd` and the shape fact `hshape` that success forces `#[.reg _, .reg _]`. -/
private theorem riscv_binaryReg_char {rop : Riscv}
    {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    (hfwd : ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
        (r₀ r₁ : Data.RISCV.Reg) (bo : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props rt #[.reg r₀, .reg r₁] bo mem
          = some (.ok (#[.reg (f r₀ r₁)], mem, none)))
    (hshape : ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
        (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
        (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
        Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) → ∃ r₀ r₁, ops = #[.reg r₀, .reg r₁]) :
    ∀ (props : HasDialectOpInfo.propertiesOf rop) (rt : Array TypeAttr)
      (ops : Array RuntimeValue) (bo : Array BlockPtr) (mem : MemoryState)
      (res : Array RuntimeValue × MemoryState × Option ControlFlowAction),
      Riscv.interpretOp' rop props rt ops bo mem = some (.ok res) →
      ∃ r₀ r₁, ops = #[.reg r₀, .reg r₁] ∧ res = (#[.reg (f r₀ r₁)], mem, none) := by
  intro props rt ops bo mem res h
  obtain ⟨r₀, r₁, rfl⟩ := hshape props rt ops bo mem res h
  rw [hfwd props rt r₀ r₁ bo mem] at h
  exact ⟨r₀, r₁, rfl, by injection h with h; injection h with h; exact h.symm⟩

/-! ### `drop_ext_binary_low_word` instantiations (`drop_zextw_addw`, `drop_sextw_addw`) -/

theorem drop_zextw_addw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_binary_low_word_local .zextw .addw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_binary_low_word_local .zextw .addw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_binary_low_word_local .zextw .addw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_binary_low_word_local .zextw .addw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_binary_low_word_local .zextw .addw) h h₂ h₃ h₄ :=
  drop_ext_binary_low_word_local_preservesSemantics (ext := .zextw) (dst := .addw)
    (extFn := Data.RISCV.zextw) (dstFn := fun a b => Data.RISCV.addw b a)
    (fun hType => OperationPtr.Pure.riscv_zextw hType)
    (riscv_ext_char (extFn := Data.RISCV.zextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (riscv_binaryReg_char (f := fun a b => Data.RISCV.addw b a)
      (fun _ _ r₀ r₁ _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r₀ r₁ heq; exact ⟨r₀, r₁, Array.toList_inj.mp heq⟩
        all_goals exact absurd h (by simp)))
    (fun _ r₀ r₁ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun a b => Data.RISCV.drop_zextw_addw_rs1)
    (fun a b => Data.RISCV.drop_zextw_addw_rs2)

theorem drop_sextw_addw_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps (drop_ext_binary_low_word_local .sextw .addw)}
    {h₂ : LocalRewritePattern.ReturnCtxChanges (drop_ext_binary_low_word_local .sextw .addw)}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds (drop_ext_binary_low_word_local .sextw .addw)}
    {h₄ : LocalRewritePattern.ReturnValues (drop_ext_binary_low_word_local .sextw .addw)} :
    LocalRewritePattern.PreservesSemantics (drop_ext_binary_low_word_local .sextw .addw) h h₂ h₃ h₄ :=
  drop_ext_binary_low_word_local_preservesSemantics (ext := .sextw) (dst := .addw)
    (extFn := Data.RISCV.sextw) (dstFn := fun a b => Data.RISCV.addw b a)
    (fun hType => OperationPtr.Pure.riscv_sextw hType)
    (riscv_ext_char (extFn := Data.RISCV.sextw)
      (fun _ _ r _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r heq; exact ⟨r, Array.toList_inj.mp heq⟩
        · exact absurd h (by simp)))
    (riscv_binaryReg_char (f := fun a b => Data.RISCV.addw b a)
      (fun _ _ r₀ r₁ _ _ => by simp [Riscv.interpretOp', pure, Interp])
      (fun _ _ _ _ _ _ h => by
        simp only [Riscv.interpretOp', pure, Interp] at h
        split at h
        · rename_i r₀ r₁ heq; exact ⟨r₀, r₁, Array.toList_inj.mp heq⟩
        all_goals exact absurd h (by simp)))
    (fun _ r₀ r₁ _ _ => by simp [Riscv.interpretOp', pure, Interp])
    (fun a b => Data.RISCV.drop_sextw_addw_rs1)
    (fun a b => Data.RISCV.drop_sextw_addw_rs2)
private theorem matchSelect_baseType_eq_tvType {ctx : WfIRContext OpCode} (_ctxDom : ctx.Dom)
    (ctxVerif : ctx.Verified) {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {base cond tv fv : ValuePtr} {selOp : OperationPtr}
    (hDef : getDefiningOp base ctx.raw = some selOp)
    (hSel : matchSelect selOp ctx.raw = some (cond, tv, fv))
    (hOperand : base ∈ op.getOperands! ctx.raw) :
    (base.getType! ctx.raw).val = (tv.getType! ctx.raw).val := by
  obtain ⟨hSelType, hSelNumResults, hSelOperands⟩ := matchSelect_implies hSel
  obtain ⟨basePtr, rfl⟩ : ∃ p, base = ValuePtr.opResult p := by
    cases base with
    | opResult p => exact ⟨p, rfl⟩
    | _ => simp [getDefiningOp] at hDef
  have hSelOpEq : basePtr.op = selOp := by simp [getDefiningOp] at hDef; grind
  subst hSelOpEq
  have hBaseIn : (ValuePtr.opResult basePtr).InBounds ctx.raw := by grind
  have hSelOpIn : basePtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : basePtr.index < basePtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hBaseEq : basePtr = basePtr.op.getResult 0 := by
    have hidx : basePtr.index = 0 := by omega
    cases basePtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hSelVerified : basePtr.op.Verified ctx hSelOpIn := by grind
  obtain ⟨-, -, -, hResEqT, -⟩ := OperationPtr.Verified.llvm_select hSelVerified hSelType
  have hTvEq : tv = (basePtr.op.getOperands! ctx.raw)[1]! := by rw [hSelOperands]; rfl
  have hOperand1 : basePtr.op.getOperand! ctx.raw 1 = tv := by
    rw [hTvEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hBaseTypeEq : (ValuePtr.opResult basePtr).getType! ctx.raw
      = ((basePtr.op.getResult 0).get! ctx.raw).type := by rw [hBaseEq]; rfl
  rw [hBaseTypeEq, hResEqT, hOperand1]

/-! ### select_of_truncate

  `trunc (select c t f) → select c (trunc t) (trunc f)`. `op` is the `trunc`, whose operand is a
  defining `select c t f`. Mirrors `select_of_zext` but narrowing (`i64 → i32`); since `llvm.trunc`
  has no `Verified` bundle, `v0`'s type is transferred from the `select`'s arm via
  `matchSelect_baseType_eq_tvType`, and the emitted `trunc`s only *refine* `Int.trunc`.
-/

set_option maxHeartbeats 1000000 in
theorem select_of_truncate_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps select_of_truncate_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges select_of_truncate_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds select_of_truncate_local}
    {h₄ : LocalRewritePattern.ReturnValues select_of_truncate_local} :
    LocalRewritePattern.PreservesSemantics select_of_truncate_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, select_of_truncate_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [pure] at hpattern
  -- Peel `matchTrunc` (op is the zext).
  have hMatchSome : (matchTrunc op ctx.raw).isSome := by
    cases hM : matchTrunc op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨v0, tp⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  obtain ⟨hOpType, hNumResults, hOperands, hTProps⟩ := matchTrunc_implies hMatch
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have hv0Eq : v0 = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = v0 := by
    rw [hv0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hv0In : v0 ∈ op.getOperands! ctx.raw := by rw [hOperands]; simp
  -- Peel the defining `select`.
  have hDefSome : (getDefiningOp v0 ctx.raw).isSome := by
    cases hM : getDefiningOp v0 ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨dS, hDef⟩ := Option.isSome_iff_exists.mp hDefSome
  rw [hDef] at hpattern
  simp only [] at hpattern
  have hSelSome : (matchSelect dS ctx.raw).isSome := by
    cases hM : matchSelect dS ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨cond, tv, fv⟩, hSel⟩ := Option.isSome_iff_exists.mp hSelSome
  rw [hSel] at hpattern
  simp only [] at hpattern
  -- `v0`'s declared type equals `tv`'s (the `select`'s arm), and the pattern guards force both
  -- to be `i64`, the `op` result to be `i32`. `llvm.trunc` has no `Verified` bundle.
  have hBaseTvType := matchSelect_baseType_eq_tvType ctxDom ctxVerif opInBounds hDef hSel hv0In
  -- `tv`'s type is an integer type (guarded in the pattern).
  obtain ⟨tvty, hTvTypeVal⟩ : ∃ t, (tv.getType! ctx.raw).val = Attribute.integerType t := by
    cases hr : (tv.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  have hV0Type : (v0.getType! ctx.raw).val = Attribute.integerType tvty := by
    rw [hBaseTvType, hTvTypeVal]
  -- `op`'s result type is an integer type (guarded in the pattern).
  obtain ⟨retty, hResType⟩ : ∃ t, ((op.getResult 0).get! ctx.raw).type.val
      = Attribute.integerType t := by
    cases hr : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hTvTypeVal, hr] at hpattern; simp at hpattern
  -- Recover the `select`'s value and `t`/`f`'s facts.
  obtain ⟨cv, tvv, fvv, hcVal, htVal, hfVal, hv0SelIs, hCondType, hTvType, hFvType, hDomC, hDomT,
      hDomF, hCIn, hTIn, hFIn, cNotOp, tNotOp, fNotOp⟩ :=
    matchSelect_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDef hSel
      (by rw [hOperands]; simp) hV0Type
  -- Width guards: `tv`/`v0` are `i64`, `op`'s result is `i32`. Collapse them now so the unfold's
  -- narrowing side-condition (`retType < opType`) and the widths align.
  rw [hTvTypeVal, hResType] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hOW
  split at hpattern
  case isFalse =>
    change some (ctx, none) = _ at hpattern
    injection hpattern with hp; injection hp with _ hp2; exact absurd hp2 (by simp)
  rename_i hRW
  obtain ⟨ow⟩ := tvty; simp only at hOW hTvTypeVal hV0Type; subst hOW
  obtain ⟨rw'⟩ := retty; simp only at hRW hResType; subst hRW
  -- Unfold `op` (the trunc), giving `op`'s result = `trunc v0v`.
  have hwTR : (IntegerType.mk 32).bitwidth < (IntegerType.mk 64).bitwidth := by decide
  obtain ⟨v0v, hv0Val, hMem, hOpResVal, hCf⟩ :=
    matchTruncOp_interpretOp_unfold (props := tp)
      opInBounds hOpType hNumResults hOperands hTProps
      (show op.getResultTypes! ctx.raw
          = #[⟨.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩] by
        have hResTypeAttr : ((op.getResult 0).get! ctx.raw).type
            = (⟨.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) :=
          Subtype.ext hResType
        apply Array.ext
        · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
        · intro i h1 h2
          simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults] at h1
          obtain rfl : i = 0 := by omega
          have := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctx.raw)
            (index := 0) (by omega)
          grind)
      hwTR (by intro w₁ resTy hw' xx pp hIsTy bo mem
               simp [Llvm.interpretOp', ge_iff_le, Nat.not_le.mpr hw', pure, Interp])
      hinterp hV0Type
  subst hCf
  -- Pin `v0v = select cv tvv fvv` (both readings of `v0`'s value).
  obtain rfl : v0v = Data.LLVM.Int.select cv tvv fvv := by
    have := hv0Val.symm.trans hv0SelIs; simpa using this
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hOpResVal] at hsourceValues
  subst sourceValues
  -- Type attrs.
  have hOutTyAttr : (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw
      = (⟨Attribute.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_opResult]; exact Subtype.ext hResType
  have hOpRes0In : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    have hnr : op.getNumResults! ctx.raw = 1 := hNumResults
    clear valueRefinement state'Dom state'Wf hpattern hOpResVal
    rw [ValuePtr.inBounds_opResult]
    refine ⟨opInBounds, ?_⟩
    simp only [OperationPtr.getResult]; grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hTvTypeAttr : tv.getType! ctx.raw
      = (⟨Attribute.integerType ⟨64⟩, hTvType ▸ (tv.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hTvType
  have hCondTypeAttr : cond.getType! ctx.raw
      = (⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr) :=
    Subtype.ext hCondType
  -- Peel the three creations (`zext tv`, `zext fv`, `select cond zt zf`).
  peelOpCreation!₂ hpattern ctx₁ trtOp hTrt hDomT hDomT₁ hDomF hDomF₁
  have hDomC₁ : cond.dominatesIp (InsertPoint.before op) ctx₁ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hTrt
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomC
  peelOpCreation!₂ hpattern ctx₂ trfOp hTrf hDomF₁ hDomF₂ hDomC₁ hDomC₂
  have hDomT₂ : tv.dominatesIp (InsertPoint.before op) ctx₂ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hTrf
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomT₁
  peelOpCreation!₂ hpattern ctx₃ selNewOp hSelNew hDomC₂ hDomC₃ hDomF₂ hDomF₃
  have hDomT₃ : tv.dominatesIp (InsertPoint.before op) ctx₃ :=
    (ValuePtr.dominatesIp_before_WfRewriter_createOp hSelNew
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)
      (by clear valueRefinement state'Dom state'Wf hpattern; grind)).mpr hDomT₂
  cleanupHpattern hpattern
  have hTrtNeTrf : trtOp ≠ trfOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hTrtNeSel : trtOp ≠ selNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  have hTrfNeSel : trfOp ≠ selNewOp := by clear hpattern state'Wf state'Dom valueRefinement; grind
  -- Transports.
  have hOutTyAttr₁ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
      = (⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hTrt hOpRes0In]; exact hOutTyAttr
  have hOutTyAttr₂ : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
      = (⟨Attribute.integerType ⟨32⟩, by grind⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hTrf
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hTrt hOpRes0In)]
    exact hOutTyAttr₁
  -- Structural facts for `zext tv`.
  have hTrtType : trtOp.getOpType! ctx₃.raw = .llvm .trunc := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTrt (operation := trtOp),
      OperationPtr.getOpType!_WfRewriter_createOp hTrf (operation := trtOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := trtOp)]
  have hTrtOperands : trtOp.getOperands! ctx₃.raw = #[tv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTrt (operation := trtOp),
      OperationPtr.getOperands!_WfRewriter_createOp hTrf (operation := trtOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := trtOp)]
  have hTrtProps : trtOp.getProperties! ctx₃.raw (.llvm .trunc) = tp := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hTrt (operation := trtOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hTrf hTrtNeTrf,
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSelNew hTrtNeSel]
  have hTrtResTypes : trtOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hTrt (operation := trtOp)
    rw [if_pos rfl] at hT
    have hT2 := OperationPtr.getResultTypes!_WfRewriter_createOp hTrf (operation := trtOp)
    rw [if_neg hTrtNeTrf] at hT2
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := trtOp)
    rw [if_neg hTrtNeSel] at hT3
    rw [hT3, hT2, hT]
    exact congrArg (fun t => #[t]) hOutTyAttr
  -- Structural facts for `zext fv`.
  have hTrfType : trfOp.getOpType! ctx₃.raw = .llvm .trunc := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hTrf (operation := trfOp),
      OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := trfOp)]
  have hTrfOperands : trfOp.getOperands! ctx₃.raw = #[fv] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hTrf (operation := trfOp),
      OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := trfOp)]
  have hTrfProps : trfOp.getProperties! ctx₃.raw (.llvm .trunc) = tp := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hTrf (operation := trfOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hSelNew hTrfNeSel]
  have hTrfResTypes : trfOp.getResultTypes! ctx₃.raw
      = #[(⟨Attribute.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] := by
    have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hTrf (operation := trfOp)
    rw [if_pos rfl] at hT
    have hT3 := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := trfOp)
    rw [if_neg hTrfNeSel] at hT3
    rw [hT3, hT]
    exact congrArg (fun t => #[t]) hOutTyAttr
  -- Structural facts for the `select`.
  have hSelNewType : selNewOp.getOpType! ctx₃.raw = .llvm .select := by
    grind [OperationPtr.getOpType!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewOperands : selNewOp.getOperands! ctx₃.raw
      = #[cond, ValuePtr.opResult (trtOp.getResult 0), ValuePtr.opResult (trfOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewNumResults : selNewOp.getNumResults! ctx₃.raw = 1 := by
    grind [OperationPtr.getNumResults!_WfRewriter_createOp hSelNew (operation := selNewOp)]
  have hSelNewCondType : cond.getType! ctx₃.raw
      = (⟨Attribute.integerType ⟨1⟩, hCondType ▸ (cond.getType! ctx.raw).2⟩ : TypeAttr) := by
    rw [ValuePtr.getType!_WfRewriter_createOp_of_inBounds hSelNew
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hTrf
          (WfRewriter.createOp_inBounds_mono (ptr := .value _) hTrt hCIn)),
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hTrf
        (WfRewriter.createOp_inBounds_mono (ptr := .value _) hTrt hCIn),
      ValuePtr.getType!_WfRewriter_createOp_of_inBounds hTrt hCIn]
    exact hCondTypeAttr
  -- Read refined `cond`/`tv`/`fv`.
  obtain ⟨ct, hCVal', hcRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hCIn hcVal
      hDomC hDomC₃ cNotOp
  obtain ⟨tt, hTVal', htRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hTIn htVal
      hDomT hDomT₃ tNotOp
  obtain ⟨ft, hFVal', hfRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hFIn hfVal
      hDomF hDomF₃ fNotOp
  -- Replay the two `zext`s, then the `select`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
    interpretOp_llvm_unaryInt_forward (state := state') (inBounds := by grind)
      (srcType := ⟨64⟩) (resType := ⟨32⟩)
      (f := fun c => Data.LLVM.Int.trunc c 32 tp.nsw tp.nuw (by omega))
      (by intro blockOperands mem
          simp [Llvm.interpretOp', pure, Interp])
      hTrtType hTrtProps hTrtOperands hTrtResTypes hTVal'
  have hFVal₁ : s₁.variables.getVar? fv = some (RuntimeValue.int 64 ft) := by
    rw [hFrame₁ fv (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hFIn
      (WfRewriter.createOp_new_not_inBounds trtOp hTrt))]
    exact hFVal'
  have hCVal₁ : s₁.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₁ cond (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hCIn
      (WfRewriter.createOp_new_not_inBounds trtOp hTrt))]
    exact hCVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
    interpretOp_llvm_unaryInt_forward (state := s₁) (inBounds := by grind)
      (srcType := ⟨64⟩) (resType := ⟨32⟩)
      (f := fun c => Data.LLVM.Int.trunc c 32 tp.nsw tp.nuw (by omega))
      (by intro blockOperands mem
          simp [Llvm.interpretOp', pure, Interp])
      hTrfType hTrfProps hTrfOperands hTrfResTypes hFVal₁
  have hTrtResIn₁ : (ValuePtr.opResult (trtOp.getResult 0)).InBounds ctx₁.raw := by
    have hnr : trtOp.getNumResults! ctx₁.raw = 1 := by
      grind [OperationPtr.getNumResults!_WfRewriter_createOp hTrt (operation := trtOp)]
    clear valueRefinement state'Dom state'Wf hpattern
    rw [ValuePtr.inBounds_opResult]
    refine ⟨WfRewriter.createOp_new_inBounds trtOp hTrt, ?_⟩
    simp only [OperationPtr.getResult]
    grind [OperationPtr.getNumResults!, OperationPtr.get!]
  have hTrtRes₂ : s₂.variables.getVar? (ValuePtr.opResult (trtOp.getResult 0))
      = some (RuntimeValue.int 32 (Data.LLVM.Int.trunc tt 32 tp.nsw tp.nuw (by omega))) := by
    rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hTrtResIn₁
      (WfRewriter.createOp_new_not_inBounds trfOp hTrf))]
    exact hRes₁
  have hCVal₂ : s₂.variables.getVar? cond = some (RuntimeValue.int 1 ct) := by
    rw [hFrame₂ cond (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds
      (WfRewriter.createOp_inBounds_mono (ptr := .value cond) hTrt hCIn)
      (WfRewriter.createOp_new_not_inBounds trfOp hTrf))]
    exact hCVal₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_llvm_select_forward (state := s₂) (inBounds := by grind)
      (it := ⟨32⟩) hSelNewType hSelNewOperands
      (show selNewOp.getResultTypes! ctx₃.raw
          = #[(⟨Attribute.integerType ⟨32⟩, hResType ▸ ((op.getResult 0).get! ctx.raw).type.2⟩ : TypeAttr)] by
        have hT := OperationPtr.getResultTypes!_WfRewriter_createOp hSelNew (operation := selNewOp)
        rw [if_pos rfl] at hT; rw [hT]; exact congrArg (fun t => #[t]) hOutTyAttr)
      hCVal₂ hTrtRes₂ hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 32 (Data.LLVM.Int.select ct
      (Data.LLVM.Int.trunc tt 32 tp.nsw tp.nuw (by omega)) (Data.LLVM.Int.trunc ft 32 tp.nsw tp.nuw (by omega)))],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Assemble: `zext (select cv tvv fvv) ⊒ select cv (zext tvv) (zext fvv) ⊒ select ct (zext tt) (zext ft)`.
  simp only [Data.LLVM.Int.cast_self]
  exact isRefinedBy_trans (Data.LLVM.Int.select_of_truncate_rw (s := tp.nsw) (u := tp.nuw))
    (Data.LLVM.Int.select_mono _ _ _ _ _ _
      (Data.LLVM.Int.trunc_mono tvv tt (by omega) htRef)
      (Data.LLVM.Int.trunc_mono fvv ft (by omega) hfRef) hcRef)

end Veir.RISCV
