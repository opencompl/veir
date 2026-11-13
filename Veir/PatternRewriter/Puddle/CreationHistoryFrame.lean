module

public import Veir.PatternRewriter.Puddle.DriverScope
public import Veir.PatternRewriter.Puddle.CreationCheckedSemantics
public import Veir.Interpreter.CTreeEquationLemma
import all Veir.PatternRewriter.Puddle.CreationCheckedSemantics
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.CTree
import all CTree.Defs
import all Veir.PatternRewriter.Puddle.Execution

namespace Veir
public section

/-- A successful checked opcode changes only its own result slots, regardless of its effects. -/
theorem CTree.interpretOpCore_preserves_lookup {ctx : WfIRContext OpCode}
    {op : OperationPtr} {state final : InterpreterState ctx} {action : Option ControlFlowAction}
    {opIn : op.InBounds ctx.raw} {value : ValuePtr}
    (notResult : value ∉ op.getResults! ctx.raw)
    (outcome : PureOrErr.CanInterpretTo (interpretOpCore op state opIn) (.ok (final, action))) :
    final.variables.getVar? value = state.variables.getVar? value := by
  unfold interpretOpCore runOpWith at outcome
  split at outcome
  · rcases (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp outcome with ⟨raw, _, committed⟩ | h | h
    · unfold commitOpResults at committed
      split at committed
      · rename_i variables hset
        have equal := PureOrErr.CanInterpretTo.pure_iff _ _ |>.mp committed
        cases equal
        exact VariableState.getVar?_setResultValues?_of_notMem_getResults! notResult hset
      · simp [fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at committed
    all_goals simp_all
  · simp [fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at outcome

namespace Puddle.CTree

/-- A successful checked batch preserves any slot disjoint from every result vector it writes. -/
theorem interpretCreatedOpsChecked_preserves_lookup {ctx : WfIRContext OpCode}
    (ops : List OperationPtr) {state final : InterpreterState ctx} {value : ValuePtr}
    (disjoint : ∀ op ∈ ops, value ∉ op.getResults! ctx.raw)
    (outcome : PureOrErr.CanInterpretTo (interpretCreatedOpsChecked ctx ops state) (.ok final)) :
    final.variables.getVar? value = state.variables.getVar? value := by
  induction ops generalizing state with
  | nil =>
    have equal := PureOrErr.CanInterpretTo.pure_iff _ _ |>.mp outcome
    cases equal
    rfl
  | cons op ops ih =>
    simp only [interpretCreatedOpsChecked] at outcome
    split at outcome
    · rcases (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp outcome with ⟨⟨middle, action⟩, head, tail⟩ | h | h
      · exact (ih (fun op member => disjoint op (List.mem_cons_of_mem _ member)) tail).trans
          (Veir.CTree.interpretOpCore_preserves_lookup (disjoint op (by simp)) head)
      all_goals simp_all
    · simp [fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at outcome

/-- The checked finite batch has only finite choice, interpreter failure, or UB nodes. -/
theorem interpretCreatedOpsChecked_pureOrErr {ctx : WfIRContext OpCode}
    (ops : List OperationPtr) (state : InterpreterState ctx) :
    PureOrErr (interpretCreatedOpsChecked ctx ops state) := by
  induction ops generalizing state with
  | nil => exact .ret _
  | cons op ops ih =>
    simp only [interpretCreatedOpsChecked]
    split
    · apply PureOrErr.bind _ _ (Veir.CTree.interpretOpCore_pureOrErr _ _ _)
      intro next
      exact ih next.1
    · simp [fail, _root_.CTree.CTree.trigger_def]
      exact .fail


/-- Fresh allocation prevents every new operation result from aliasing any old bounded pointer,
even when the lookup context is the final driver context where the root has been erased. -/
theorem Pattern.interpret_created_results_disjoint_source (rule : Veir.Puddle.Pattern OpCode)
    {source created target : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (run : rule.interpret source root = some (created, some (newOps, replacements)))
    {op : OperationPtr} (member : op ∈ newOps) {value : ValuePtr}
    (valueIn : value.InBounds source.raw) : value ∉ op.getResults! target.raw := by
  have fresh := ((rule.interpret_structure run).1 op).mp member |>.2
  intro result
  obtain ⟨index, _, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp result
  apply fresh
  rw [← equal] at valueIn
  grind

/-- Every successful checked execution of the actual created list preserves all old SSA slots. -/
theorem Pattern.interpret_checked_preserves_source_lookups (rule : Veir.Puddle.Pattern OpCode)
    {source created target : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (run : rule.interpret source root = some (created, some (newOps, replacements)))
    {before after : InterpreterState target}
    (outcome : PureOrErr.CanInterpretTo
      (interpretCreatedOpsChecked target newOps.toList before) (.ok after)) :
    ∀ value, value.InBounds source.raw →
      after.variables.getVar? value = before.variables.getVar? value := by
  intro value valueIn
  apply interpretCreatedOpsChecked_preserves_lookup _ _ outcome
  intro op member
  exact Pattern.interpret_created_results_disjoint_source rule run (by simpa using member) valueIn

/-- Keep the old-slot frame as a postcondition of the actual checked batch simulation. The
successful-outcome witness comes from finite primitive semantics, with no determinism assumption. -/
theorem Pattern.interpret_checked_sim_preserves_source_lookups (rule : Veir.Puddle.Pattern OpCode)
    {source created target : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (run : rule.interpret source root = some (created, some (newOps, replacements)))
    (before : InterpreterState target) :
    _root_.CTree.Sim (fun after other => after = other ∧
      ∀ value, value.InBounds source.raw →
        after.variables.getVar? value = before.variables.getVar? value)
      (interpretCreatedOpsChecked target newOps.toList before)
      (interpretCreatedOpsChecked target newOps.toList before) := by
  apply (PureOrErr.sim_with_outcome (interpretCreatedOpsChecked_pureOrErr newOps.toList before)).mono
  rintro after other ⟨equal, outcome⟩
  exact ⟨equal, Pattern.interpret_checked_preserves_source_lookups rule run outcome⟩


/-- Enrich any local-root simulation with the checked batch's original-slot frame. -/
theorem Pattern.interpret_checked_sim_with_source_lookups (rule : Veir.Puddle.Pattern OpCode)
    {source created target : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (run : rule.interpret source root = some (created, some (newOps, replacements)))
    (before : InterpreterState target) {γ : Type} {original : Tree γ}
    {relation : InterpreterState target → γ → Prop}
    (simulation : _root_.CTree.Sim relation
      (interpretCreatedOpsChecked target newOps.toList before) original) :
    _root_.CTree.Sim (fun after original => relation after original ∧
      ∀ value, value.InBounds source.raw →
        after.variables.getVar? value = before.variables.getVar? value)
      (interpretCreatedOpsChecked target newOps.toList before) original := by
  apply (Pattern.interpret_checked_sim_preserves_source_lookups rule run before).trans simulation
  rintro after middle original ⟨rfl, frame⟩ related
  exact ⟨related, frame⟩

end Puddle.CTree
end
end Veir
