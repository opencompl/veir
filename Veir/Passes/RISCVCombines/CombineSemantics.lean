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

end Veir.RISCV
