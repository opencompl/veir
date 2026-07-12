import Veir.Interpreter.EquationLemma
import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas

/-!
# Monotonicity of the interpreter

This file proves the monotonicity of `interpretOp`, `interpretOpList`, and
`interpretTerminatedOpList` under a cross-context interpreter state
refinement. This result is the key to prove the correctness of many transformations, as the
interpreter state refinement relation can be used to then prove the refinement of functions and
modules.

## Monotonicity of `interpretOp`
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
    (opVerif' : op'.Verified ctx' opIn')
    (notStore : op.getOpType! ctx.raw ≠ .llvm .store)
    (notFreeze : op.getOpType! ctx.raw ≠ .llvm .freeze)
    (notBitcast : op.getOpType! ctx.raw ≠ .llvm .bitcast)
    (notCast : op.getOpType! ctx.raw ≠ .builtin .unrealized_conversion_cast) :
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
    operands operands' (op.getSuccessors! ctx.raw) state.memory notStore notFreeze notBitcast
    notCast hOpsRef
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
  · /- If the source interpretation returns UB, then the refinement holds trivially. -/
    simp


/-!
## Monotonicity of `interpretOpList` and `interpretTerminatedOpList`

Lifts the per-operation monotonicity lemma `interpretOp_monotone` to lists of operations
(`interpretOpList` / `interpretTerminatedOpList`), under a *cross-context* interpreter-state
refinement over an *identical* list of operations modulus α-renaming
(`ValueMapping.PreservesOperation`) of operands and results. -/

/-- `interpretOpList` is monotone under a *cross-context* interpreter-state refinement, over an
*identical* slice of a block operation chain (the same `OperationPtr`s, whose intrinsic data agrees
modulo renaming `mapping`). -/
theorem interpretOpList_mono
    {ctx ctx' : WfIRContext OpCode} (hVerif : ctx'.Verified)
    {ops : List OperationPtr}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    {mapping : ValueMapping ctx ctx'}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op)
    (notStore : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .store)
    (notFreeze : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .freeze)
    (notBitcast : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .bitcast)
    (notCast : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .builtin .unrealized_conversion_cast) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList ops state) (interpretOpList ops state') := by
  induction ops generalizing state state' with
  | nil => simpa [Interp]
  | cons a l ih =>
    /- Refinement of the state after interpreting the head operation `a`. -/
    have refinesHead := interpretOp_monotone (opsInBounds a (by grind)) (opsInBounds' a (by grind))
      hState (hPreserves a (by grind)) (by grind) (notStore a (by grind)) (notFreeze a (by grind))
      (notBitcast a (by grind)) (notCast a (by grind))
    simp only [interpretOpList_cons]
    /- Case analysis on the interpretation of the head operation `a` in the source. -/
    rcases hsrc : interpretOp a state (opsInBounds a (by grind)) with _ | (⟨s, act⟩ | _)
    · /- Source operation fails: interpreting the list returns `none`, refinement is trivial. -/
      simp [Interp.isRefinedBy]
    · /- Source operation succeeds with new state `s` and action `act`. This means that the target
      operation also succeeds with a refined state `s'` and action `act'`. -/
      simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at refinesHead
      obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := refinesHead
      simp only [htgt]
      /- Case analysis on the action. -/
      cases act
      case none =>
        /- No control-flow action: recurse on the tail, advancing the target invariant past `a`.
        We use the induction to handle the tail. -/
        have hact' : act' = none := by grind [ControlFlowAction.optionIsRefinedBy]
        subst hact'
        simp only
        apply ih (by grind) (by grind) hsRef (by grind) (by grind) (by grind) (by grind) (by grind)
      case some cf =>
        simp [ControlFlowAction.optionIsRefinedBy] at hactRef
        /- A control-flow action: the list stops here for both the source and the target. -/
        have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by grind
        subst hact'
        simp [Interp, hsRef, ControlFlowAction.optionIsRefinedBy, hcfRef]
    · /- Source operation is UB, which is refined by anything. -/
      simp

/-- `interpretTerminatedOpList` is monotone under a *cross-context* interpreter-state refinement,
over an *identical* list of operations. The proof is derived from `interpretOpList_monotone`, as
`interpretTerminatedOpList` is a wrapper around `interpretOpList` that checks that the list of
operation has reached a terminator. -/
theorem interpretTerminatedOpList_mono
    {ctx ctx' : WfIRContext OpCode} (ctx'Verif : ctx'.Verified)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hFrame : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op)
    (notStore : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .store)
    (notFreeze : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .freeze)
    (notBitcast : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .llvm .bitcast)
    (notCast : ∀ op, op ∈ ops → op.getOpType! ctx.raw ≠ .builtin .unrealized_conversion_cast) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState ctx' × ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList ops state) (interpretTerminatedOpList ops state') := by
  have hList := interpretOpList_mono ctx'Verif opsInBounds opsInBounds' hState hFrame notStore
    notFreeze notBitcast notCast
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList ops state (by grind) with _ | (⟨s, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hList
    obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := hList
    simp only [htgt]
    /- Case analysis on the action returned by `interpretOpList`. If no action is returned at the
    source, then the refinement is trivial (as interpretation failed in the input). If an action
    is returned, then we derive refinement from the refinement of the action (given by
    `interpretOpList_mono`). -/
    cases act with
    | none =>  simp [Interp.isRefinedBy]
    | some cf =>
      have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
        cases act' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst hact'
      exact ⟨hsRef, hcfRef⟩
  · exact Interp.isRefinedBy_ub_target

end Veir
