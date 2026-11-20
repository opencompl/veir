module

public import Veir.Passes.Legalization.Validity.PhiEntry
public import Veir.Passes.Legalization.Validity.Brcond
import Veir.Interpreter.Lemmas
import all Veir.Passes.Legalization.Validity.PhiEntry
import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.IR.Basic
import all Veir.IR.InBounds
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.Passes.Legalization.Validity.PhiFrame
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.InstructionSelection.Branches.Pass

public section
namespace Veir.Legalization.CTreeProofs.PhiWidening
open _root_.CTree Veir.CTree
variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

/-- A chunk comprises one original operation and all its incoming-edge extensions. -/
def ChunkSim (op : OperationPtr) (opIn : op.InBounds src.raw) : Prop :=
  ∀ (s : InterpreterState src) (t : InterpreterState dst), W.StateRel s t →
    ∀ tIn : ∀ o ∈ extensionsBefore W.updates op ++ [op], o.InBounds dst.raw,
    Sim W.OpRel (opListTree (extensionsBefore W.updates op ++ [op]) t tIn)
      (interpretOperationTree op s opIn)

/-- Chunk simulations compose for any list of operations, including a block terminated by a
conditional branch that chooses an edge other than the one being widened. -/
private theorem sim_list (chunks : ∀ op (opIn : op.InBounds src.raw), W.ChunkSim op opIn)
    (ops : List OperationPtr) (srcIn : ∀ o ∈ ops, o.InBounds src.raw)
    (dstIn : ∀ o ∈ ops.flatMap (fun op => extensionsBefore W.updates op ++ [op]), o.InBounds dst.raw)
    (s : InterpreterState src) (t : InterpreterState dst) (rel : W.StateRel s t) :
    Sim W.OpRel (opListTree _ t dstIn) (opListTree ops s srcIn) := by
  induction ops generalizing s t with
  | nil =>
    simp only [List.flatMap_nil, opListTree_nil]
    exact (Sim.pure _ _ _).mpr ⟨rel, trivial⟩
  | cons op rest ih =>
    rw [opListTree_congr (List.flatMap_cons ..), opListTree_append, opListTree_cons]
    apply sim_tau1_right
    rw [tree_bind_eq, tree_bind_eq]
    refine Sim.bind _ _ _ _ (chunks op (srcIn op (by simp)) s t rel _) ?_
    rintro ⟨t', act'⟩ ⟨s', act⟩ ⟨states, actions⟩
    cases act <;> cases act' <;> dsimp only [opListCont, Option.elim] at *
    · exact ih _ _ _ _ states
    · contradiction
    · rename_i cf; cases cf <;> contradiction
    · exact (Sim.pure _ _ _).mpr ⟨states, actions⟩

theorem bodySim_of_chunks (chunks : ∀ op (opIn : op.InBounds src.raw), W.ChunkSim op opIn) :
    W.BodySim := by
  intro b bIn s t rel dstIn
  exact W.sim_list chunks _ _ dstIn s t rel

theorem preserves_unmodified {op : OperationPtr} (opIn : op.InBounds src.raw)
    (untouched : ∀ u ∈ W.updates, u.operand.op ≠ op) :
    W.mapping.PreservesOperation op op opIn (W.opHeader opIn).inBounds := by
  have before := W.truncations.ops op opIn
  have same := before.trans_id (W.extensions.opSame before.inBounds (fun u hu => Ne.symm (untouched u hu)))
  have count : op.getNumResults! dst.raw = op.getNumResults! src.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, same.resultTypes,
      OperationPtr.getResultTypes!.size_eq_getNumResults!]
  have mapped {vs : Array ValuePtr} (h : ∀ v ∈ vs, v.InBounds src.raw) :
      W.mapping.applyToArray vs h = vs.map W.mapValue := by
    simp [mapping, ValueMapping.applyToArray]
  refine ⟨same.opType, ?_, same.resultTypes, same.successors, ?_, ?_, ?_⟩
  · rw [same.properties]
    exact OperationPtr.getProperties!_cast same.opType
  · rw [mapped]; exact same.operands
  · rw [mapped]
    simp [OperationPtr.getResults!, count, mapValue, lowerArgs, OperationPtr.getResult_def]
  · intro v vin i h
    change W.mapValue v = op.getResult i at h
    cases v with
    | opResult r => exact h
    | blockArgument a =>
      simp only [mapValue, lowerArgs] at h
      split at h
      next selected =>
        obtain ⟨⟨j, w⟩, hj, rfl⟩ := List.mem_map.mp selected
        obtain ⟨_, _, _, fresh, _⟩ := W.truncations.args j w hj
        have eq := congrArg OpResultPtr.op (ValuePtr.opResult.inj h)
        change W.cast ⟨block, j⟩ = op at eq
        exact (fresh (eq ▸ opIn)).elim
      next => contradiction

private theorem actionRel_of_unmodified {action action' : Option ControlFlowAction}
    (standard : ControlFlowAction.optionIsRefinedBy action action')
    (outside : ∀ vs, action = some (.branch vs block) → args = []) :
    W.ActionRel action action' := by
  cases action with
  | none => cases action' <;> first | trivial | contradiction
  | some a =>
    cases action' with
    | none => contradiction
    | some b =>
      cases a with
      | «return» vs => cases b <;> first | exact standard | contradiction
      | branch vs dest =>
        cases b with
        | «return» => contradiction
        | branch vt dest' =>
          obtain ⟨rfl, refin⟩ := standard
          refine ⟨rfl, refin.1, fun i hi => ?_⟩
          by_cases atPhi : dest = block
          · subst dest
            have empty := outside vs rfl
            simpa [ArgumentRel, selectedArgs, empty] using refin.2 i hi
          · simpa [ArgumentRel, selectedArgs, BlockPtr.getArgument_def, Ne.symm atPhi] using refin.2 i hi

/-- An original operation with unchanged branch slots is simulated under the argument-to-truncation
mapping. Its branch, if any, forwards ordinary refined values to an unchanged destination. -/
theorem unmodifiedChunk {op : OperationPtr} (opIn : op.InBounds src.raw)
    (mono : op.TreeMonotone src)
    (untouched : ∀ u ∈ W.updates, u.operand.op ≠ op)
    (outside : block ∈ op.getSuccessors! src.raw → args = []) : W.ChunkSim op opIn := by
  intro s t rel tIn
  have noExt : extensionsBefore W.updates op = [] := by
    simpa [extensionsBefore, List.filter_eq_nil_iff] using untouched
  rw [opListTree_congr (show extensionsBefore W.updates op ++ [op] = [op] by simp [noExt]),
    opListTree_cons]
  apply sim_tau1_left
  have passthrough (r : InterpreterState dst × Option ControlFlowAction) :
      r.2.elim (opListTree [] r.1 (by simp)) (fun cf => pure (r.1, some cf)) = pure r := by
    rcases r with ⟨state, _ | cf⟩ <;> simp [opListTree_nil]
  rw [show (fun r : InterpreterState dst × Option ControlFlowAction => r.2.elim
    (opListTree [] r.1 (by simp)) (fun cf => pure (r.1, some cf))) = pure from funext passthrough,
    _root_.bind_pure]
  have sim := interpretOperationTree_sim_of_preservesOperation opIn (W.opHeader opIn).inBounds mono rel
    (W.preserves_unmodified opIn untouched)
  cases lifted : (op.getOpType! src.raw).isLifted with
  | false =>
    apply sim_mono sim
    rintro t' s' ⟨states, actions, _, none⟩
    exact ⟨states, W.actionRel_of_unmodified actions (fun _ h => by simp [none lifted] at h)⟩
  | true =>
    rw [interpretOperationTree_eq_monadLift s opIn lifted] at sim ⊢
    apply sim_monadLift
    rintro ⟨s', act⟩ run
    rw [run] at sim
    apply sim_mono (sim_pure_and sim (P := fun r => interpretOp op s opIn = .ok r) run)
    rintro t' ⟨s'', act'⟩ ⟨⟨states, actions, _⟩, step⟩
    refine ⟨states, W.actionRel_of_unmodified actions ?_⟩
    rintro vs rfl
    exact outside (interpretOp_branch_dest_mem_getSuccessors! step)

end Veir.Legalization.CTreeProofs.PhiWidening
