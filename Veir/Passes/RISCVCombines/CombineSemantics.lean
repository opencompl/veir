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

end Veir.RISCV
