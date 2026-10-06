module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Verifier

import Veir.Interpreter.Lemmas
import Veir.Dialects.Monotonicity
import Veir.Interpreter.EquationLemma
import Veir.Interpreter.Refinement.Lemmas

public section

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

/-!
## Monotonicity of calls
-/

/-- A refinement of a value conforms to every type the value conforms to. -/
theorem RuntimeValue.Conforms.of_isRefinedBy {v v' : RuntimeValue} {ty : TypeAttr}
    (h : v.Conforms ty) (href : v ⊒ v') : v'.Conforms ty := by
  rcases ty with ⟨ty, hty⟩
  cases v <;> cases v' <;> cases ty <;>
    simp_all [RuntimeValue.Conforms, RuntimeValue.isRefinedBy] <;> grind

theorem RuntimeValue.ArrayConforms.of_arrayIsRefinedBy {vals vals' : Array RuntimeValue}
    {types : Array TypeAttr} (h : ArrayConforms vals types) (href : vals ⊒ vals') :
    ArrayConforms vals' types :=
  ⟨by grind [ArrayConforms, RuntimeValue.arrayIsRefinedBy], fun i hi =>
    (h.2 i (by grind [RuntimeValue.arrayIsRefinedBy])).of_isRefinedBy
      (href.2 i (by grind [RuntimeValue.arrayIsRefinedBy]))⟩

/-- Performing a call is monotone in the outcome of the operation and in the call semantics. -/
theorem CallSemantics.perform_isRefinedBy {call call' : CallSemantics}
    (hcall : call.isRefinedBy call')
    {r r' : Array RuntimeValue × MemoryState × Option ControlFlowAction}
    (h : OperationResult.isRefinedBy r r') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (call.perform r.1 r.2.1 r.2.2) (call'.perform r'.1 r'.2.1 r'.2.2) := by
  obtain ⟨results, mem, action⟩ := r
  obtain ⟨results', mem', action'⟩ := r'
  obtain ⟨hresults, rfl, haction⟩ := h
  rcases action with _ | ⟨_ | _ | ⟨callee, args⟩⟩ <;>
    rcases action' with _ | ⟨_ | _ | ⟨callee', args'⟩⟩ <;>
    simp_all [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
      CallSemantics.perform, OperationResult.isRefinedBy]
  obtain ⟨rfl, hargs⟩ := haction
  have := hcall callee args args' mem hargs
  rcases hsource : call callee args mem with _ | _ | ⟨mem₂, results₂⟩ <;>
    simp_all [FunctionResult.isRefinedBy]
  obtain ⟨mem₂', results₂', htarget, rfl, hresults₂⟩ := this
  simp only [htarget, Interp.bind_ok]
  exact ⟨_, _, _, rfl, hresults₂, rfl, trivial⟩

/-- Interpreting an operation and performing its call is monotone in the call semantics. -/
theorem OperationPtr.interpretWith_isRefinedBy {call call' : CallSemantics}
    (hcall : call.isRefinedBy call') {op op' : OperationPtr} {ctx ctx' : IRContext OpCode}
    {operands operands' : Array RuntimeValue} {mem : MemoryState}
    (h : Interp.isRefinedBy OperationResult.isRefinedBy (op.interpret ctx operands mem)
      (op'.interpret ctx' operands' mem)) :
    Interp.isRefinedBy OperationResult.isRefinedBy (op.interpretWith call ctx operands mem)
      (op'.interpretWith call' ctx' operands' mem) := by
  simp only [OperationPtr.interpretWith]
  rcases hsource : op.interpret ctx operands mem with _ | _ | r
  · simp
  · simp
  · rw [hsource, Interp.isRefinedBy_ok_target_iff] at h
    obtain ⟨r', htarget, hr⟩ := h
    simp only [htarget, Interp.bind_ok]
    exact CallSemantics.perform_isRefinedBy hcall hr

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
theorem interpretOp_monotone {call call' : CallSemantics} (hcall : call.isRefinedBy call')
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : mapping.PreservesOperation op op') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp call op state opIn)
      (interpretOp call' op' state' opIn') := by
  /- Do a case analysis on the source interpretation. If it fails or is UB, then the refinement is
     trivial. -/
  rcases hsrc : interpretOp call op state opIn with _ | _ | ⟨state₂, act⟩
  · simp [Interp.isRefinedBy]
  · simp
  /- Otherwise, the source operands are defined, so are the target ones, and memory is equal. -/
  obtain ⟨operands, -, -, -, hSrcOps, -⟩ := interpretOp_some_iff.mp hsrc
  obtain ⟨resValues, hinterp', hResValues⟩ :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2 opIn hPreserves.operands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  /- Interpreting the operation and performing its call is monotone in the operands, and in the
     call semantics. -/
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  have hPR : Interp.isRefinedBy OperationResult.isRefinedBy
      (op.interpretWith call ctx.raw operands state.memory)
      (op'.interpretWith call' ctx'.raw operands' state'.memory) := by
    rw [hMem] at hInterp'Eq ⊢
    apply OperationPtr.interpretWith_isRefinedBy hcall
    rw [hInterp'Eq, ← hMem]
    exact interpretOp'_monotone (op.getOpType! ctx.raw)
      (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
      operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  simp only [hinterp', Interp.isRefinedBy_ok_target_iff, OperationResult.isRefinedBy,
    Prod.exists] at hPR
  obtain ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, rfl, actRef⟩ := hPR
  /- The target results refine the source results, which conform to the result types since the
     source could bind them, so the target can bind them too. -/
  have hconforms : RuntimeValue.ArrayConforms resValues' (op'.getResultTypes! ctx'.raw) := by
    rw [hPreserves.resultTypes]
    exact ((VariableState.setResultValues?_isSome_iff_conforms state.variables opIn).mpr
      ⟨_, hResValues⟩).of_arrayIsRefinedBy resValuesRef
  have stateVarRef : state.variables.isRefinedBy state'.variables mapping := by
    grind [InterpreterState.isRefinedBy]
  obtain ⟨v, hv, hvRef⟩ := VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef
    hPreserves.results hPreserves.reflect hResValues hconforms opIn'
  simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
  exact ⟨⟨v, state₂.memory⟩, act',
    (interpretOp_ok_iff_of_getOperandValues_eq_some hTgtOps).mpr ⟨resValues', hinterp'Tgt, hv⟩,
    ⟨rfl, hvRef⟩, actRef⟩

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
    {call call' : CallSemantics} (hcall : call.isRefinedBy call')
    {ctx ctx' : WfIRContext OpCode} {ops : List OperationPtr}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    {mapping : ValueMapping ctx ctx'}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList call ops state) (interpretOpList call' ops state') := by
  induction ops generalizing state state' with
  | nil => simpa using hState
  | cons a l ih =>
    /- Refinement of the state after interpreting the head operation `a`. -/
    have refinesHead := interpretOp_monotone hcall (opsInBounds a (by grind))
      (opsInBounds' a (by grind)) hState (hPreserves a (by grind))
    simp only [interpretOpList_cons]
    /- Case analysis on the interpretation of the head operation `a` in the source. -/
    rcases hsrc : interpretOp call a state (opsInBounds a (by grind)) with _ | _ | ⟨s, act⟩
    · /- Source operation fails: interpreting the list returns `.fail`, refinement is trivial. -/
      simp [Interp.isRefinedBy]
    · /- Source operation is UB, which is refined by anything. -/
      simp
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
        apply ih (by grind) (by grind) hsRef (by grind)
      case some cf =>
        simp [ControlFlowAction.optionIsRefinedBy] at hactRef
        /- A control-flow action: the list stops here for both the source and the target. -/
        have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by grind
        subst hact'
        simp [hsRef, ControlFlowAction.optionIsRefinedBy, hcfRef]

/-- `interpretTerminatedOpList` is monotone under a *cross-context* interpreter-state refinement,
over an *identical* list of operations. The proof is derived from `interpretOpList_monotone`, as
`interpretTerminatedOpList` is a wrapper around `interpretOpList` that checks that the list of
operation has reached a terminator. -/
theorem interpretTerminatedOpList_mono
    {call call' : CallSemantics} (hcall : call.isRefinedBy call')
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hFrame : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState ctx' × ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList call ops state) (interpretTerminatedOpList call' ops state') := by
  have hList := interpretOpList_mono hcall opsInBounds opsInBounds' hState hFrame
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList call ops state (by grind) with _ | _ | ⟨s, act⟩
  · simp [Interp.isRefinedBy]
  · exact Interp.isRefinedBy_ub_target
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

end Veir
