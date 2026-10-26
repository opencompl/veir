module

public import Veir.Interpreter.CTreeRefinement.Monotonicity
public import Veir.Interpreter.Lemmas

import all Veir.Interpreter.VariableState

public section

namespace Veir.DCE

/-- Refining a runtime value preserves its declared type. -/
theorem conforms_of_refines {source target : RuntimeValue} {type : TypeAttr}
    (hrefines : RuntimeValue.isRefinedBy source target) (hconforms : source.Conforms type) :
    target.Conforms type := by
  cases source <;> cases target <;>
    simp_all [RuntimeValue.isRefinedBy, RuntimeValue.Conforms]
  all_goals
    rcases type with ⟨type, htype⟩
    cases type <;> simp_all <;> grind

/-- Pointwise refinement preserves an array's declared result types. -/
theorem arrayConforms_of_refines {source target : Array RuntimeValue}
    {types : Array TypeAttr} (hrefines : RuntimeValue.arrayIsRefinedBy source target)
    (hconforms : RuntimeValue.ArrayConforms source types) :
    RuntimeValue.ArrayConforms target types := by
  refine ⟨hrefines.1.symm.trans hconforms.1, ?_⟩
  intro index hindex
  have hsize := hrefines.1
  exact conforms_of_refines (hrefines.2 index (by omega))
    (hconforms.2 index (by omega))

/-- Relate source definitions only for values that remain relevant after DCE.
This requires no total map from deleted source values into the target context. -/
def VariablesRefineOn {ctxSource ctxTarget : WfIRContext OpCode}
    (live : ValuePtr → Prop) (source : VariableState ctxSource)
    (target : VariableState ctxTarget) : Prop :=
  ∀ value, live value → ∀ sourceValue, source.getVar? value = some sourceValue →
    ∃ targetValue, target.getVar? value = some targetValue ∧
      RuntimeValue.isRefinedBy sourceValue targetValue

/-- State refinement restricted to surviving values, with refining memory. -/
def StatesRefineOn {ctxSource ctxTarget : WfIRContext OpCode}
    (live : ValuePtr → Prop) (source : InterpreterState ctxSource)
    (target : InterpreterState ctxTarget) : Prop :=
  Tree.Refinement.MemoryState.isRefinedBy source.memory target.memory ∧
    VariablesRefineOn live source.variables target.variables

/-- Fresh function variable states are related for every surviving-value set. -/
theorem variablesRefineOn_empty (ctxSource ctxTarget : WfIRContext OpCode)
    (live : ValuePtr → Prop) :
    VariablesRefineOn live (.empty ctxSource) (.empty ctxTarget) := by
  intro value _ sourceValue hvalue
  simp [VariableState.getVar?, VariableState.empty] at hvalue

/-- An unchanged surviving operation reads related operand arrays. -/
theorem getOperandValues_refineOn
    {ctxSource ctxTarget : WfIRContext OpCode}
    {source : VariableState ctxSource} {target : VariableState ctxTarget}
    {live : ValuePtr → Prop} {operation : OperationPtr} {sourceValues : Array RuntimeValue}
    (hstate : VariablesRefineOn live source target)
    (hoperands : operation.getOperands! ctxTarget.raw = operation.getOperands! ctxSource.raw)
    (hlive : ∀ value ∈ operation.getOperands! ctxSource.raw, live value)
    (hsource : source.getOperandValues operation = some sourceValues) :
    ∃ targetValues, target.getOperandValues operation = some targetValues ∧
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues := by
  have hsourceMap : (operation.getOperands! ctxSource.raw).mapM source.getVar? =
      some sourceValues := hsource
  obtain ⟨targetValues, htarget⟩ := Array.mapM_option_isSome
    (f := target.getVar?) (l := operation.getOperands! ctxTarget.raw) (by
      intro index hindex
      have hsourceIndex := Array.mapM_option_eq_some_implies hsourceMap index (by grind)
      have hliveIndex := hlive ((operation.getOperands! ctxSource.raw)[index]'(by grind))
        (by grind)
      obtain ⟨value, hvalue, _⟩ := hstate _ hliveIndex _ hsourceIndex
      have htargetIndex : target.getVar? (operation.getOperands! ctxTarget.raw)[index] =
          some value := by simpa only [hoperands] using hvalue
      simp only [htargetIndex, Option.isSome_some])
  refine ⟨targetValues, htarget, ?_⟩
  constructor
  · grind
  · intro index hindex
    have hsourceIndex := Array.mapM_option_eq_some_implies hsourceMap index hindex
    have htargetIndex := Array.mapM_option_eq_some_implies htarget index (by grind)
    have hliveIndex := hlive ((operation.getOperands! ctxSource.raw)[index]'(by grind))
      (by grind)
    obtain ⟨value, hvalue, hrefines⟩ := hstate _ hliveIndex _ hsourceIndex
    grind

/-- Updating only discarded results preserves every live source definition. -/
theorem variablesRefineOn_setDiscardedResults
    {ctxSource ctxTarget : WfIRContext OpCode}
    {source nextSource : VariableState ctxSource} {target : VariableState ctxTarget}
    {live : ValuePtr → Prop} {operation : OperationPtr} {results : Array RuntimeValue}
    {operationIn : operation.InBounds ctxSource.raw}
    (hstate : VariablesRefineOn live source target)
    (hdiscarded : ∀ value, live value → value ∉ operation.getResults! ctxSource.raw)
    (hset : source.setResultValues? operation results operationIn = some nextSource) :
    VariablesRefineOn live nextSource target := by
  intro value hvalue sourceValue hsourceValue
  have hunchanged := VariableState.getVar?_setResultValues?_of_notMem_getResults!
    (hdiscarded value hvalue) hset
  rw [hunchanged] at hsourceValue
  exact hstate value hvalue sourceValue hsourceValue

/-- Updating a surviving operation's related results preserves live definitions. -/
theorem variablesRefineOn_setResults
    {ctxSource ctxTarget : WfIRContext OpCode}
    {source nextSource : VariableState ctxSource}
    {target nextTarget : VariableState ctxTarget}
    {live : ValuePtr → Prop} {operation : OperationPtr}
    {sourceResults targetResults : Array RuntimeValue}
    {sourceIn : operation.InBounds ctxSource.raw} {targetIn : operation.InBounds ctxTarget.raw}
    (hstate : VariablesRefineOn live source target)
    (hsourceIn : ∀ value, live value → value.InBounds ctxSource.raw)
    (htargetIn : ∀ value, live value → value.InBounds ctxTarget.raw)
    (hresults : RuntimeValue.arrayIsRefinedBy sourceResults targetResults)
    (hsource : source.setResultValues? operation sourceResults sourceIn = some nextSource)
    (htarget : target.setResultValues? operation targetResults targetIn = some nextTarget) :
    VariablesRefineOn live nextSource nextTarget := by
  intro value hlive sourceValue hvalue
  have hsourceLookup := VariableState.getVar?_setResultValues?_of_value_inBounds
    (hsourceIn value hlive) hsource
  have htargetLookup := VariableState.getVar?_setResultValues?_of_value_inBounds
    (htargetIn value hlive) htarget
  rw [hsourceLookup] at hvalue
  rw [htargetLookup]
  rcases value with ⟨valueOp, index⟩ | argument
  · by_cases hop : valueOp = operation
    · subst valueOp
      simp at hvalue
      refine ⟨targetResults[index]!, by simp, ?_⟩
      have hsize := VariableState.setResultValues?.getNumRseults!_eq_size hsource
      have hin := hsourceIn (.opResult ⟨operation, index⟩) hlive
      have hindex : index < sourceResults.size := by
        simp only [ValuePtr.inBounds_opResult, OpResultPtr.inBounds_def] at hin
        grind
      have hrefines := hresults.2 index hindex
      grind
    · simp only [hop, ↓reduceIte] at hvalue ⊢
      exact hstate (.opResult ⟨valueOp, index⟩) hlive sourceValue hvalue
  · exact hstate (.blockArgument argument) hlive sourceValue hvalue

/-- Binding related arguments in the same surviving block preserves live values. -/
theorem variablesRefineOn_setArguments
    {ctxSource ctxTarget : WfIRContext OpCode}
    {source nextSource : VariableState ctxSource}
    {target nextTarget : VariableState ctxTarget}
    {live : ValuePtr → Prop} {block : BlockPtr}
    {sourceValues targetValues : Array RuntimeValue}
    {sourceIn : block.InBounds ctxSource.raw} {targetIn : block.InBounds ctxTarget.raw}
    (hstate : VariablesRefineOn live source target)
    (harguments : block.getNumArguments! ctxTarget.raw = block.getNumArguments! ctxSource.raw)
    (hsize : sourceValues.size = block.getNumArguments! ctxSource.raw)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hsource : source.setArgumentValues? block sourceValues sourceIn = some nextSource)
    (htarget : target.setArgumentValues? block targetValues targetIn = some nextTarget) :
    VariablesRefineOn live nextSource nextTarget := by
  intro value hlive sourceValue hvalue
  have hsourceLookup := VariableState.getVar?_setArgumentValues? (value := value) hsource
  have htargetLookup := VariableState.getVar?_setArgumentValues? (value := value) htarget
  rw [hsourceLookup] at hvalue
  rw [htargetLookup]
  rcases value with result | ⟨valueBlock, index⟩
  · exact hstate (.opResult result) hlive sourceValue hvalue
  · rw [harguments]
    by_cases hset : valueBlock = block ∧ index < block.getNumArguments! ctxSource.raw
    · simp only [hset] at hvalue ⊢
      refine ⟨targetValues[index]!, rfl, ?_⟩
      have hrefines := hvalues.2 index (by omega)
      grind
    · simp only [hset, ↓reduceIte] at hvalue ⊢
      exact hstate (.blockArgument ⟨valueBlock, index⟩) hlive sourceValue hvalue

end Veir.DCE
