import Veir.Interpreter.EquationLemma
import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas

/-! # Monotonicity of the interpreter

This file proves the monotonicity of `interpretOp` under a cross-context interpreter state
refinement. This result is the key to prove the correctness of many transformations, as the
interpreter state refinement relation can be used to then prove the refinement of functions and
modules.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}

/-- `VariableState.getOperandValues` is monotone with respect to the state refinement relation:
refined variable states produce refined operand arrays. -/
theorem VariableState.getOperandValues_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'} {mapping : ValueMapping ctx ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) (opIn : op.InBounds ctx.raw)
    (hOperands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw))
    (hSrc : srcVars.getOperandValues op = some srcVal) :
    ∃ tgtVal, tgtVars.getOperandValues op' = some tgtVal ∧ srcVal ⊒ tgtVal := by
  simp only [VariableState.isRefinedBy] at hRef
  have ⟨hsize, hSrc⟩ := VariableState.getOperandValues_eq_some_iff.mp hSrc
  have hSrc₂ := Array.mapM_option_isSome (f := tgtVars.getVar?) (l := op'.getOperands! ctx'.raw)
  have ⟨r, hr⟩ := hSrc₂ (by grind [ValueMapping.applyToArray])
  simp only [getOperandValues, hr, Option.some.injEq, exists_eq_left']
  simp only [RuntimeValue.arrayIsRefinedBy]
  constructor
  · grind
  · intro i hi
    grind [Array.mapM_option_eq_some_implies hr i (by grind), ValueMapping.applyToArray]

/-- `setResultValues?` preserves the state refinement. If the source/target variable states are
related by `mapping`, the freshly-computed result values refine (`resValues ⊒ resValues'`), `op`
and `op'` have the same results related by `mapping` (`hResults` and `hReflect`), then the target
`setResultValues?` also succeeds and the states after binding the results are again related by
`mapping`. -/
theorem VariableState.setResultValues?_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) {newSrcVars : VariableState ctx}
    {srcVals tgtVals : Array RuntimeValue} (hVals : srcVals ⊒ tgtVals)
    (hResults : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw))
    (hReflect : mapping.ReflectsResults op op')
    (hSrc : srcVars.setResultValues? op srcVals opIn = some newSrcVars)
    (tgtValsConforms : RuntimeValue.ArrayConforms tgtVals (op'.getResultTypes! ctx'.raw))
    (opIn' : op'.InBounds ctx'.raw) :
    ∃ newTgtVars, tgtVars.setResultValues? op' tgtVals opIn' = some newTgtVars ∧
                  newSrcVars.isRefinedBy newTgtVars mapping := by
  /- Conformance of the (refined) target values implies target success. -/
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms
      (varState := tgtVars) (inBounds := opIn')).mp tgtValsConforms
  simp only [hTgt, Option.some.injEq, exists_eq_left']
  /- Reason per element in the source and result value arrays. -/
  intro val valIn sv hsv
  /- Do a case analysis on whether or not the value is one of `op` results.
  If it is not, the value is not a result of `op'`, and the refinement follows from the
  original `VariableState` refinement.
  If it is, then because of `hReflect`, the value is mapped to a result of `op'`, and the
  refinement follows the `RuntimeValue` array refinement. -/
  cases OperationPtr.getResults!_not_mem_or_eq_getResult ctx.raw val op
  next hNotMem => grind [VariableState.isRefinedBy]
  next hMem =>
    have hfix := ValueMapping.applyToArray_getResults!_ext opIn hResults.symm
    grind [RuntimeValue.arrayIsRefinedBy]

/--
`interpretOp` is monotone under a *cross-context* interpreter-state refinement.

Lift `interpretOp'_monotone` through `getOperandValues` and `setResultValues?`. The source state
lives in `ctx`, the target in `ctx'`, related by `InterpreterState.isRefinedBy` through the value
renaming `mapping` (for the unchanged majority, `mapping` is the identity-on-`ValuePtr` `InBounds`-embedding).

The conclusion relates the two `interpretOp` results: their interpreter states are again related by
`InterpreterState.isRefinedBy mapping`, and their control flow actions by `ControlFlowAction`-refinement.
Because the state relation constrains only values defined in *both* states, `op`'s freshly-set
results are added on both sides and re-established by `interpretOp'_monotone`, while pre-existing
values stay defined and refined.
-/
theorem interpretOp_monotone
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : mapping.PreservesOperation op op')
    (opVerif' : op'.Verified ctx' opIn') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  -- If the source interpretation fails, then the refinement is trivial
  by_cases hsource : interpretOp op state opIn = none; simp [hsource, Interp.isRefinedBy]
  -- Source/target operands are defined, and memory is equal.
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2 opIn hPreserves.operands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  -- Add the refinement of `interpretOp'` on `op` with `operands` and `operands'`
  have hPR1 := interpretOp'_monotone (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  -- Add the equality between `interpretOp'` on `operands'`
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  /- Do a case analysis on the source interpretation -/
  rcases hsrc : interpretOp op state opIn with _ | (⟨state₂, act⟩ | _)
  · -- If the source interpretation fails, then the refinement is trivial
    simp [Interp.isRefinedBy]
  · /- If the source interpretation returns a new state, we need to prove that (1) the target
       interpretation also returns a new state, and (2) the new states are in the refinement relation. -/
    simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
    have ⟨resValues, hinterp', hResValues⟩ :=
      (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [hinterp', Interp.isRefinedBy_ok_target_iff, Prod.exists] at hPR1
    have ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, memoryEq, actRef⟩ := hPR1
    subst memory'₂
    simp only [← hInterp'Eq] at hinterp'Tgt
    simp only [interpretOp, hTgtOps, bind, hinterp'Tgt, liftM, monadLift, MonadLift.monadLift]
    have := interpretOp'_results_conform (opInBounds := opIn') opVerif' (VariableState.getOperandValues_conforms hTgtOps) hinterp'Tgt
    have ⟨v, hv⟩ := (VariableState.setResultValues?_isSome_iff_conforms state'.variables opIn').mp this
    simp only [Interp, hv, pure, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq]
    have stateVarRef : state.variables.isRefinedBy state'.variables mapping := by grind [InterpreterState.isRefinedBy]
    grind [InterpreterState.isRefinedBy, VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef, cases ValueMapping.PreservesOperation]
  · /- If the source interpretation returns UB, then we need to prove that the target
       interpretation does not fail. -/
    simp only [Interp.isRefinedBy_ub_target_iff]
    rcases htgt : interpretOp op' state' opIn' with _ | (⟨state₂', act'⟩ | _)
    /- If the target is either UB or a result, then the refinement is trivial. -/
    rotate_left; grind; grind
    have hinterp' := (interpretOp_ub_iff_op_interpret_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [interpretOp, OperationPtr.interpret, hTgtOps, hPreserves.resultTypes, hPreserves.successors, ← hMem, liftM, monadLift,
      MonadLift.monadLift] at htgt
    simp only [Interp.isRefinedBy, hinterp'] at hPR1
    split at hPR1; grind; rotate_left; grind; grind
    rename_i _ _ interpTgtRes _ hInterpTgtRes
    simp [interpretOp'_opType_cast hPreserves.opType hPreserves.props, hInterpTgtRes, bind] at htgt
    cases interpTgtRes
    · simp only [pure] at htgt
      simp only [← hInterp'Eq] at hInterpTgtRes
      have := interpretOp'_results_conform (opInBounds := opIn') opVerif' (VariableState.getOperandValues_conforms hTgtOps) hInterpTgtRes
      split at htgt
      · grind [VariableState.setResultValues?_isSome_iff_conforms (varState := state'.variables)]
      · grind
      · grind
    · grind
