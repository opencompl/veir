import Veir.Fold.Bridge
import Veir.Fold.Materialize
import Veir.PatternRewriter.Semantics

/-!
  # End-to-end correctness of the folding rewrite

  This file connects the decision-level folding theorems to the actual local
  rewrite used by canonicalization.
-/

namespace Veir

theorem foldDecision_resultTypes_size_eq_one
    {opCode : OpCode} {properties : HasOpInfo.propertiesOf opCode}
    {resultTypes : Array TypeAttr} {knownOperands : Array (Option RuntimeValue)}
    {decision : FoldDecision}
    (hDecision : foldDecision opCode properties resultTypes knownOperands = decision)
    (hNotNoFold : decision ≠ .noFold) : resultTypes.size = 1 := by
  unfold foldDecision at hDecision
  split at hDecision
  · exact absurd hDecision (by simpa using hNotNoFold.symm)
  · split at hDecision
    · exact absurd hDecision (by simpa using hNotNoFold.symm)
    · grind

theorem WfRewriter.materializeConstant!_withCreatedOps
    {ctx ctx' : WfIRContext OpCode} {rv : RuntimeValue} {resType : TypeAttr}
    {forOp : OpCode} {newOp : OperationPtr}
    (hMat : WfRewriter.materializeConstant! ctx rv resType forOp = some (ctx', newOp)) :
    WfIRContext.WithCreatedOps ctx ctx' := by
  unfold WfRewriter.materializeConstant! at hMat
  repeat' split at hMat
  all_goals try simp at hMat
  all_goals
    obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
      WfRewriter.createOp!_some_inv hMat
    exact .CreatedOp ctx ctx ctx' (.Nil ctx)
      ⟨_, _, _, _, _, _, _, _, _, _, hCreate⟩

theorem WfRewriter.materializeConstant!_newOp_iff
    {ctx ctx' : WfIRContext OpCode} {rv : RuntimeValue} {resType : TypeAttr}
    {forOp : OpCode} {newOp : OperationPtr}
    (hMat : WfRewriter.materializeConstant! ctx rv resType forOp = some (ctx', newOp))
    (candidate : OperationPtr) :
    candidate.InBounds ctx'.raw ∧ ¬candidate.InBounds ctx.raw ↔ candidate = newOp := by
  unfold WfRewriter.materializeConstant! at hMat
  repeat' split at hMat
  all_goals try simp at hMat
  all_goals
    obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
      WfRewriter.createOp!_some_inv hMat
    constructor
    · intro h
      grind [WfRewriter.createOp]
    · rintro rfl
      exact ⟨WfRewriter.createOp_new_inBounds candidate hCreate,
        WfRewriter.createOp_new_not_inBounds candidate hCreate⟩

theorem WfRewriter.materializeConstant!_result_inBounds
    {ctx ctx' : WfIRContext OpCode} {rv : RuntimeValue} {resType : TypeAttr}
    {forOp : OpCode} {newOp : OperationPtr}
    (hMat : WfRewriter.materializeConstant! ctx rv resType forOp = some (ctx', newOp)) :
    (ValuePtr.opResult (newOp.getResult 0)).InBounds ctx'.raw := by
  unfold WfRewriter.materializeConstant! at hMat
  repeat' split at hMat
  all_goals try simp at hMat
  all_goals
    obtain ⟨hoper, hblock, hreg, hins, hCreate⟩ :=
      WfRewriter.createOp!_some_inv hMat
    grind

/-- Exact successful-result shapes of `foldOperationLocal`. -/
inductive FoldOperationLocal.Match (ctx : WfIRContext OpCode) (op : OperationPtr) :
    WfIRContext OpCode → Array OperationPtr → Array ValuePtr → Prop where
  | operand (opInBounds : op.InBounds ctx.raw) (j : Nat) (operand : ValuePtr)
      (hDecision : foldDecision (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw)
        ((op.getOperands! ctx.raw).map (ValuePtr.constantValue · ctx.raw)) = .useOperand j)
      (hOperand : (op.getOperands! ctx.raw)[j]? = some operand) :
      Match ctx op ctx #[] #[operand]
  | constant (opInBounds : op.InBounds ctx.raw) (rv : RuntimeValue) (resultType : TypeAttr)
      (ctx' : WfIRContext OpCode) (newOp : OperationPtr)
      (hDecision : foldDecision (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw)
        ((op.getOperands! ctx.raw).map (ValuePtr.constantValue · ctx.raw)) = .useConstant rv)
      (hResultType : (op.getResultTypes! ctx.raw)[0]? = some resultType)
      (hMat : WfRewriter.materializeConstant! ctx rv resultType
        (op.getOpType! ctx.raw) = some (ctx', newOp)) :
      Match ctx op ctx' #[newOp] #[newOp.getResult 0]

theorem FoldOperationLocal.Match.of_eq
    (hPattern : foldOperationLocal ctx op = some (newCtx, some (newOps, newValues))) :
    FoldOperationLocal.Match ctx op newCtx newOps newValues := by
  simp only [foldOperationLocal] at hPattern
  split at hPattern
  · split at hPattern
    · simp at hPattern
    · split at hPattern
      · simp at hPattern
        obtain ⟨rfl, rfl, rfl⟩ := hPattern
        exact .operand (by assumption) _ _ (by assumption) (by assumption)
      · simp at hPattern
    · rename_i _ rv hDecision
      split at hPattern
      · rename_i resultType hResultType
        cases hMat : WfRewriter.materializeConstant! ctx rv resultType
            (op.getOpType! ctx.raw) with
        | none => simp [hMat] at hPattern
        | some result =>
          simp [hMat, pure] at hPattern
          obtain ⟨rfl, rfl, rfl⟩ := hPattern
          exact .constant (by assumption) rv resultType _ _ hDecision hResultType hMat
      · simp [pure] at hPattern
  · simp at hPattern

theorem foldOperationLocal_returnsCtxNoChanges :
    LocalRewritePattern.ReturnsCtxNoChanges foldOperationLocal := by
  intro ctx op newCtx hPattern
  by_cases opInBounds : op.InBounds ctx.raw
  · rw [foldOperationLocal, dif_pos opInBounds] at hPattern
    simp only at hPattern
    split at hPattern
    · simpa using hPattern
    · split at hPattern
      · simp at hPattern
      · simpa using hPattern
    · rename_i _ rv hDecision
      split at hPattern
      · rename_i resultType hResultType
        cases hMat : WfRewriter.materializeConstant! ctx rv resultType
            (op.getOpType! ctx.raw) with
        | none => simp [hMat] at hPattern
        | some result => simp [hMat] at hPattern
      · simpa using hPattern
  · simp [foldOperationLocal, opInBounds] at hPattern
    exact hPattern

theorem foldOperationLocal_returnCtxChanges :
    LocalRewritePattern.ReturnCtxChanges foldOperationLocal := by
  intro ctx op newCtx newOps newValues hPattern
  cases FoldOperationLocal.Match.of_eq hPattern with
  | operand => exact .Nil ctx
  | constant _ _ _ _ _ _ _ hMat =>
    exact WfRewriter.materializeConstant!_withCreatedOps hMat

theorem foldOperationLocal_returnOps :
    LocalRewritePattern.ReturnOps foldOperationLocal := by
  intro ctx op newCtx newOps newValues hPattern candidate
  cases FoldOperationLocal.Match.of_eq hPattern with
  | operand => simp
  | constant _ _ _ _ _ _ _ hMat =>
    simpa using (WfRewriter.materializeConstant!_newOp_iff hMat candidate).symm

theorem foldOperationLocal_returnValues :
    LocalRewritePattern.ReturnValues foldOperationLocal := by
  intro ctx op opInBounds newCtx newOps newValues hPattern
  cases FoldOperationLocal.Match.of_eq hPattern with
  | operand _ _ _ hDecision _ | constant _ _ _ _ _ hDecision _ _ =>
    have hSize := foldDecision_resultTypes_size_eq_one hDecision (by simp)
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!] at hSize
    simpa using hSize.symm

theorem foldOperationLocal_returnValuesInBounds :
    LocalRewritePattern.ReturnValuesInBounds foldOperationLocal := by
  intro ctx op newCtx newOps newValues hPattern value hValue
  cases FoldOperationLocal.Match.of_eq hPattern with
  | operand opInBounds j operand _ hOperand =>
    simp only [Array.mem_singleton] at hValue
    subst value
    obtain ⟨hj, hOperandEq⟩ := Array.getElem?_eq_some_iff.mp hOperand
    have hMem : operand ∈ op.getOperands! ctx.raw := by
      rw [← hOperandEq]
      exact Array.getElem_mem hj
    exact OperationPtr.getOperands!_inBounds (by grind) opInBounds hMem
  | constant _ _ _ _ _ _ _ hMat =>
    simp only [Array.mem_singleton] at hValue
    subst value
    exact WfRewriter.materializeConstant!_result_inBounds hMat

theorem RuntimeValue.Conforms.refined {source target : RuntimeValue} {ty : TypeAttr}
    (hConforms : source.Conforms ty) (hRefines : source ⊒ target) : target.Conforms ty := by
  cases source <;> cases target <;>
    simp_all [RuntimeValue.Conforms, RuntimeValue.isRefinedBy]
  all_goals
    obtain ⟨rfl, _⟩ := hRefines
    obtain ⟨ty, property⟩ := ty
    cases ty <;> simp_all

theorem fold_sourceValues_eq_results {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} {state newState : InterpreterState ctx}
    {resultValues sourceValues : Array RuntimeValue}
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hSet : state.variables.setResultValues? op resultValues = some newState.variables)
    (hSource : (op.getResults ctx.raw).mapM (newState.variables.getVar? ·) = some sourceValues) :
    sourceValues = resultValues := by
  have hResultValuesSize : resultValues.size = 1 := by
    have := VariableState.setResultValues?.getNumRseults!_eq_size hSet
    omega
  have hResults : op.getResults ctx.raw = #[ValuePtr.opResult (op.getResult 0)] := by
    grind
  have hResult0 := VariableState.getVar?_getResult_of_setResultValues?
    (varState := state.variables) (varState' := newState.variables)
    (i := 0) (by omega) hSet
  rw [hResults] at hSource
  simp at hSource
  simp [hResult0] at hSource
  subst sourceValues
  exact (Array.eq_singleton_getElem! hResultValuesSize).symm

/-- Read an unchanged value through the state-refinement hypothesis of a local rewrite. -/
theorem FoldOperationLocal.exists_refined_getVar?
    {ctx newCtx : WfIRContext OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {hpattern : foldOperationLocal ctx op = some (newCtx, some (newOps, newValues))}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (opInBounds : op.InBounds ctx.raw) (opInBounds' : op.InBounds newCtx.raw)
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern foldOperationLocal_returnValuesInBounds
        foldOperationLocal_returnValues foldOperationLocal_returnCtxChanges)
      (.at (.before op)) (.at (.before op)) (by simpa using opInBounds)
        (by simpa using opInBounds'))
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) (by simpa using opInBounds'))
    {v : ValuePtr} {sourceValue : RuntimeValue}
    (vIn : v.InBounds ctx.raw) (hValue : state.variables.getVar? v = some sourceValue)
    (hDomCtx : v.dominatesIp (InsertPoint.before op) ctx)
    (hDom' : v.dominatesIp (InsertPoint.before op) newCtx)
    (hNotResult : v ∉ op.getResults! ctx.raw) :
    ∃ targetValue, state'.variables.getVar? v = some targetValue ∧ sourceValue ⊒ targetValue := by
  have ⟨targetValue, hTargetValue⟩ :=
    InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (foldOperationLocal_returnCtxChanges.valuePtr_inBounds hpattern vIn) hDom'
  refine ⟨targetValue, hTargetValue, ?_⟩
  grind [LocalRewritePattern.mapping, valueRefinement v]

set_option maxHeartbeats 2000000 in
theorem foldOperationLocal_preservesSemantics :
    LocalRewritePattern.PreservesSemantics foldOperationLocal
      foldOperationLocal_returnOps foldOperationLocal_returnCtxChanges
      foldOperationLocal_returnValuesInBounds foldOperationLocal_returnValues := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hPattern state stateWf
    newState cf hInterp
  rintro sourceValues hSourceValues state' state'Wf state'Dom
    ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hInterp
  have hMatch := FoldOperationLocal.Match.of_eq hPattern
  cases hMatch with
  | operand _ j operand hDecision hOperand =>
    have hSem := foldDecision_foldEligibleSemantics (by rw [hDecision]; simp)
    obtain ⟨actualOperands, resultValues, hOperands, hEval, hCf, hMemory, hSet⟩ :=
      interpretOp_ok_foldEvaluate hSem hInterp
    have hAgree := foldConstOperands_agree ctxDom ctxVerif opInBounds stateWf hOperands
    have hRefines := OpCode.foldDecision_refines
      (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      ((op.getOperands! ctx.raw).map (ValuePtr.constantValue · ctx.raw))
      (op.getResultTypes! ctx.raw) actualOperands hAgree
    rw [hDecision] at hRefines
    have hNumResults : op.getNumResults! ctx.raw = 1 := by
      have hSize := foldDecision_resultTypes_size_eq_one hDecision (by simp)
      simpa using (OperationPtr.getResultTypes!.size_eq_getNumResults!
        (op := op) (ctx := ctx.raw)).symm.trans hSize
    have hSourceEq : sourceValues = resultValues :=
      fold_sourceValues_eq_results (opInBounds := opInBounds) hNumResults hSet hSourceValues
    subst sourceValues
    have hResultRefines : resultValues ⊒ #[actualOperands[j]!] := by
      simpa [FoldDecision.Refines, FoldDecision.target, hEval, Interp.isRefinedBy]
        using hRefines
    obtain ⟨hj, hOperandEq⟩ := Array.getElem?_eq_some_iff.mp hOperand
    have hjNumOperands : j < op.getNumOperands! ctx.raw := by
      simpa [OperationPtr.getOperands!.size_eq_getNumOperands!] using hj
    obtain ⟨hActualSize, hActualAt⟩ :=
      VariableState.getOperandValues_eq_some_iff.mp hOperands
    have hOperandPtr : op.getOperand! ctx.raw j = operand := by
      rw [← hOperandEq]
      symm
      exact OperationPtr.getOperands!.getElem_eq_getOperand!
        (ctx := ctx.raw) (index := j)
    have hOperandValue : state.variables.getVar? operand = some actualOperands[j]! := by
      rw [← hOperandPtr]
      exact hActualAt j hjNumOperands
    have hOperandMem : operand ∈ op.getOperands! ctx.raw := by
      rw [← hOperandEq]
      exact Array.getElem_mem hj
    have operandInBounds : operand.InBounds ctx.raw :=
      OperationPtr.getOperands!_inBounds (by grind) opInBounds hOperandMem
    have hDom : operand.dominatesIp (InsertPoint.before op) ctx := by
      grind [WfIRContext.Dom.operand_dominates_op]
    have hNotResult : operand ∉ op.getResults! ctx.raw := by
      grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
        ctxDom (op₁ := op)]
    obtain ⟨targetValue, hTargetValue, hOperandRefines⟩ :=
      FoldOperationLocal.exists_refined_getVar? opInBounds opInBounds valueRefinement state'Dom operandInBounds
        hOperandValue hDom hDom hNotResult
    subst cf
    refine ⟨state', ?_, ?_, #[targetValue], ?_, ?_⟩
    · simp [interpretOpList, liftM, monadLift, MonadLift.monadLift, pure, Interp]
    · grind
    · simp [hTargetValue]
    · exact RuntimeValue.arrayIsRefinedBy_trans hResultRefines (by simpa using hOperandRefines)
  | constant _ rv resultType ctx' newOp hDecision hResultType hMat =>
    have hSem := foldDecision_foldEligibleSemantics (by rw [hDecision]; simp)
    obtain ⟨actualOperands, resultValues, hOperands, hEval, hCf, hMemory, hSet⟩ :=
      interpretOp_ok_foldEvaluate hSem hInterp
    have hAgree := foldConstOperands_agree ctxDom ctxVerif opInBounds stateWf hOperands
    have hRefines := OpCode.foldDecision_refines
      (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      ((op.getOperands! ctx.raw).map (ValuePtr.constantValue · ctx.raw))
      (op.getResultTypes! ctx.raw) actualOperands hAgree
    rw [hDecision] at hRefines
    have hNumResults : op.getNumResults! ctx.raw = 1 := by
      have hSize := foldDecision_resultTypes_size_eq_one hDecision (by simp)
      simpa using (OperationPtr.getResultTypes!.size_eq_getNumResults!
        (op := op) (ctx := ctx.raw)).symm.trans hSize
    have hSourceEq : sourceValues = resultValues :=
      fold_sourceValues_eq_results (opInBounds := opInBounds) hNumResults hSet hSourceValues
    subst sourceValues
    have hResultRefines : resultValues ⊒ #[rv] := by
      simpa [FoldDecision.Refines, FoldDecision.target, hEval, Interp.isRefinedBy]
        using hRefines
    have hResultSize : resultValues.size = 1 := by
      simpa using hResultRefines.1
    have hArrayConforms :
        RuntimeValue.ArrayConforms resultValues (op.getResultTypes! ctx.raw) :=
      RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hSet
    obtain ⟨hResultTypeInBounds, hResultTypeEq⟩ :=
      Array.getElem?_eq_some_iff.mp hResultType
    have hSourceConforms : resultValues[0]!.Conforms resultType := by
      have hConforms := hArrayConforms.2 0 (by omega)
      have hTypeEq : (op.getResultTypes! ctx.raw)[0]! = resultType := by
        rw [getElem!_pos (op.getResultTypes! ctx.raw) 0 hResultTypeInBounds]
        exact hResultTypeEq
      rwa [hTypeEq] at hConforms
    have hValueRefines : resultValues[0]! ⊒ rv := by
      rw [Array.eq_singleton_getElem! hResultSize] at hResultRefines
      exact RuntimeValue.arrayIsRefinedBy_singleton.mp hResultRefines
    have hRvConforms : rv.Conforms resultType :=
      RuntimeValue.Conforms.refined hSourceConforms hValueRefines
    have hNotModArith : ∀ mop, op.getOpType! ctx.raw ≠ .mod_arith mop := by
      intro mop hOpType
      rw [hOpType, foldEvaluate_mod_arith] at hEval
      contradiction
    obtain ⟨newOpInBounds, targetVars, hNewInterp, hNewValue⟩ :=
      WfRewriter.materializeConstant!_interpretOp hMat hRvConforms hNotModArith state'
    subst cf
    refine ⟨⟨targetVars, state'.memory⟩, ?_, ?_, #[rv], ?_, hResultRefines⟩
    · simp [interpretOpList_cons, hNewInterp, liftM, monadLift, MonadLift.monadLift,
        Interp]
    · grind
    · simp [hNewValue]

end Veir
