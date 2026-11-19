module

public import Veir.Passes.Legalization.Validity.PhiCFG

import all Veir.Passes.Legalization.Validity.PhiCFG
import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.Passes.Legalization.Validity.PhiSimulation
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.InstructionSelection.Branches.Pass
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.IR.Basic
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas

public section
namespace Veir.Legalization.CTreeProofs.PhiWidening

open _root_.CTree Veir.CTree

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

/-- The arguments whose truncations execute when entering a particular block. -/
def entryArguments (block : BlockPtr) (args : List (Nat × Nat)) (entered : BlockPtr) :
    List BlockArgumentPtr :=
  if entered = block then selectedArgs block args else []

private theorem entryArgument_selected {entered : BlockPtr} {a : BlockArgumentPtr}
    (h : a ∈ entryArguments block args entered) :
    a.block = entered ∧ a ∈ selectedArgs block args.reverse := by
  unfold entryArguments at h
  split at h
  · rename_i eq
    subst entered
    obtain ⟨⟨i, w⟩, mem, rfl⟩ := List.mem_map.mp h
    exact ⟨rfl, List.mem_map.mpr ⟨(i, w), List.mem_reverse.mpr mem, rfl⟩⟩
  · simp at h

private theorem mem_entryArguments_of_selected {entered : BlockPtr} {i : Nat}
    (h : entered.getArgument i ∈ selectedArgs block args.reverse) :
    entered.getArgument i ∈ entryArguments block args entered := by
  obtain ⟨⟨j, w⟩, mem, eq⟩ := List.mem_map.mp h
  have parent : block = entered := congrArg BlockArgumentPtr.block eq
  simp only [entryArguments, parent, ↓reduceIte]
  exact List.mem_map.mpr ⟨(j, w), List.mem_reverse.mp mem, parent ▸ eq⟩

private theorem selected_inBounds {a : BlockArgumentPtr} (h : a ∈ selectedArgs block args.reverse) :
    a.InBounds src.raw ∧ (W.cast a).InBounds dst.raw := by
  obtain ⟨⟨i, w⟩, mem, rfl⟩ := List.mem_map.mp h
  obtain ⟨argIn, _, castIn, _⟩ := W.truncations.args i w mem
  exact ⟨argIn, W.extensions.bounds (.operation _) castIn⟩

theorem entryCastsInBounds (entered : BlockPtr) :
    ∀ op ∈ (entryArguments block args entered).map W.cast, op.InBounds dst.raw := by
  intro op mem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp mem
  exact (W.selected_inBounds (entryArgument_selected ha).2).2

private structure EntryInv (source : InterpreterState src) (target : InterpreterState dst)
    (pending : List BlockArgumentPtr) : Prop where
  memory : source.memory ⊒ target.memory
  arguments : ∀ a ∈ pending, ∃ sv tv rv,
    source.variables.getVar? (.blockArgument a) = some sv ∧ sv ⊒ rv ∧
    target.variables.getVar? (.blockArgument a) = some tv ∧
    ∃ castIn : (W.cast a).InBounds dst.raw, ∀ entered : InterpreterState dst,
      entered.variables.getVar? (.blockArgument a) = some tv →
      Returns (interpretOperationTree (W.cast a) entered castIn) (SetsCastResult (W.cast a) entered rv)
  values : ∀ v, v.InBounds src.raw → ∀ sv, source.variables.getVar? v = some sv →
    (∃ a ∈ pending, v = .blockArgument a) ∨
    ∃ tv, target.variables.getVar? (W.mapValue v) = some tv ∧ sv ⊒ tv

private theorem returns_entryPrefix {source : InterpreterState src} {target : InterpreterState dst}
    {pending : List BlockArgumentPtr}
    (covers : ∀ a ∈ pending, a ∈ selectedArgs block args.reverse)
    (ready : W.EntryInv source target pending)
    (bounds : ∀ op ∈ pending.map W.cast, op.InBounds dst.raw) :
    Returns (opListTree (pending.map W.cast) target bounds)
      (fun r => r.2 = none ∧ W.StateRel source r.1) := by
  induction pending generalizing target with
  | nil =>
    simp only [List.map_nil, opListTree_nil]
    refine returns_pure.mpr ⟨rfl, ready.memory, fun v vin sv val => ?_⟩
    simpa [mapping] using ready.values v vin sv val
  | cons a pending ih =>
    obtain ⟨sv, tv, rv, readSrc, refines, readDst, castIn, execute⟩ := ready.arguments a List.mem_cons_self
    simp only [List.map_cons, opListTree_cons, returns_tau1]
    apply (execute target readDst).bind
    rintro ⟨after, action⟩ ⟨rfl, memory, vars⟩
    simp only [Option.elim_none]
    apply ih (fun b hb => covers b (List.mem_cons_of_mem _ hb))
    refine ⟨memory ▸ ready.memory, fun b hb => ?_, fun v vin val read => ?_⟩
    · obtain ⟨s, t, r, vs, ref, vt, cont⟩ := ready.arguments b (List.mem_cons_of_mem _ hb)
      exact ⟨s, t, r, vs, ref, by rw [vars]; simpa [OperationPtr.getResult_def] using vt, cont⟩
    · have mapArg : W.mapValue (.blockArgument a) = (W.cast a).getResult 0 := by
        simp [mapValue, lowerArgs, covers a List.mem_cons_self]
      rcases ready.values v vin val read with ⟨b, hb, rfl⟩ | ⟨t, lookup, ref⟩
      · rcases List.mem_cons.mp hb with rfl | hb
        · have eq : val = sv := by simpa [readSrc] using read.symm
          exact .inr ⟨rv, by rw [vars, mapArg]; simp, eq ▸ refines⟩
        · exact .inl ⟨b, hb, rfl⟩
      · by_cases eq : W.mapValue v = (W.cast a).getResult 0
        · obtain rfl := W.mapped_eq_castResult vin (covers _ List.mem_cons_self) eq
          have same : val = sv := by simpa [readSrc] using read.symm
          exact .inr ⟨rv, by rw [vars, eq]; simp, same ▸ refines⟩
        · exact .inr ⟨t, by rw [vars]; simpa [eq] using lookup, ref⟩

/-- Set the block arguments and execute the truncations at its entry. At every other block the
prefix is empty. The resulting target state represents all the source variables again. -/
theorem enterBlock {b : BlockPtr} (bIn : b.InBounds src.raw) (bIn' : b.InBounds dst.raw)
    {source : InterpreterState src} {target : InterpreterState dst}
    {vs vt : Array RuntimeValue} {variables : VariableState src}
    (states : W.StateRel source target) (sizes : vs.size = vt.size)
    (arguments : ∀ i < vs.size, W.ArgumentRel (b.getArgument i) vs[i]! vt[i]!)
    (set : source.variables.setArgumentValues? b vs bIn = some variables) :
    ∃ outVars, target.variables.setArgumentValues? b vt bIn' = some outVars ∧
      Returns (opListTree ((entryArguments block args b).map W.cast)
        ⟨outVars, target.memory⟩ (W.entryCastsInBounds b))
        (fun r => r.2 = none ∧ W.StateRel ⟨variables, source.memory⟩ r.1) := by
  have sameNum := (W.truncations.ctxSame.trans W.extensions.ctxSame).numArguments bIn
  have size : vs.size = b.getNumArguments! src.raw := by
    grind [VariableState.setArgumentValues?]
  have conforms := (VariableState.setArgumentValues?_isSome_iff_conforms source.variables
    (blockInBounds := bIn) size).mpr ⟨variables, set⟩
  obtain ⟨outVars, targetSet⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
    target.variables (values := vt) (blockInBounds := bIn') (by rw [← sizes, size, sameNum])).mp (by
      intro i hi
      rw [sameNum] at hi
      have rel := arguments i (by omega)
      unfold ArgumentRel at rel
      split at rel
      · exact rel.1
      · rename_i h
        have vin : (ValuePtr.blockArgument (b.getArgument i)).InBounds src.raw := by
          rw [ValuePtr.inBounds_blockArg]
          exact BlockPtr.arguments_inBounds src.wellFormed.inBounds bIn hi
        have typ := W.mappedType vin
        simp only [mapValue, lowerArgs, h, ↓reduceIte] at typ
        rw [typ]
        exact (conforms i hi).of_isRefinedBy rel)
  refine ⟨outVars, targetSet, W.returns_entryPrefix
    (fun _ h => (entryArgument_selected h).2) ?_ _⟩
  refine ⟨states.1, fun a ha => ?_, fun v vin sv read => ?_⟩
  · obtain ⟨sameBlock, selected⟩ := entryArgument_selected ha
    obtain ⟨argIn, _⟩ := W.selected_inBounds selected
    have id : b.getArgument a.index = a := by cases a; simp_all [BlockPtr.getArgument_def]
    have index : a.index < b.getNumArguments! src.raw := by
      obtain ⟨ownerIn, bound⟩ := BlockArgumentPtr.inBounds_def.mp argIn
      subst b
      rwa [BlockPtr.getNumArguments!_eq_getNumArguments ownerIn]
    have rel := arguments a.index (by omega)
    rw [id, ArgumentRel, ite_eq_left selected] at rel
    obtain ⟨_, rv, ref, cont⟩ := rel
    exact ⟨vs[a.index]!, vt[a.index]!, rv, id ▸ VariableState.getVar?_getArgument_of_setArgumentValues? index set,
      ref, id ▸ VariableState.getVar?_getArgument_of_setArgumentValues? (sameNum ▸ index) targetSet, cont⟩
  · by_cases inBlock : v ∈ b.getArguments! src.raw
    · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp inBlock
      by_cases selected : b.getArgument i ∈ selectedArgs block args.reverse
      · exact .inl ⟨_, mem_entryArguments_of_selected selected, rfl⟩
      · have val := VariableState.getVar?_getArgument_of_setArgumentValues? hi set
        have eq : sv = vs[i]! := by simpa [val] using read.symm
        have rel := arguments i (by omega)
        rw [ArgumentRel, ite_eq_right selected] at rel
        exact .inr ⟨vt[i]!, by
          simp only [mapValue, lowerArgs, selected, ↓reduceIte]
          exact VariableState.getVar?_getArgument_of_setArgumentValues? (sameNum ▸ hi) targetSet,
          eq ▸ rel⟩
    · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! inBlock set] at read
      obtain ⟨tv, lookup, ref⟩ := states.2 v vin sv read
      refine .inr ⟨tv, ?_, ref⟩
      rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ targetSet]
      · exact lookup
      · intro member
        obtain ⟨i, hi, eq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
        rcases v with r | a
        · simp [mapValue, lowerArgs] at eq
        · simp only [mapValue, lowerArgs] at eq
          split at eq
          · simp [OperationPtr.getResult_def] at eq
          · exact inBlock (BlockPtr.getArguments!.mem_iff_exists_index.mpr ⟨i, sameNum ▸ hi, eq⟩)

/-- The target block consists of the entry truncations followed by the original operations, each
preceded by the extensions for its own branch operands. -/
theorem operationList (slots : ∀ u ∈ W.updates, u.operand.InBounds src.raw)
    (b : BlockPtr) (bIn : b.InBounds src.raw) :
    b.opList dst (W.ctxSame.blockIn bIn) = (entryArguments block args b).map W.cast ++
      (b.opList src bIn).flatMap (fun op => extensionsBefore W.updates op ++ [op]) := by
  have middleSlots : ∀ u ∈ W.updates, u.operand.InBounds W.truncated.raw := by
    intro u hu
    obtain ⟨opIn, index⟩ := OpOperandPtr.inBounds_def.mp (slots u hu)
    have same := W.truncations.ops u.operand.op opIn
    refine OpOperandPtr.inBounds_def.mpr ⟨same.inBounds, ?_⟩
    rwa [← OperationPtr.getNumOperands!_eq_getNumOperands same.inBounds,
      ← OperationPtr.getOperands!.size_eq_getNumOperands!, same.operands, Array.size_map,
      OperationPtr.getOperands!.size_eq_getNumOperands!, OperationPtr.getNumOperands!_eq_getNumOperands opIn]
  rw [W.extensions.opList_flatMap middleSlots b (W.truncations.ctxSame.blockIn bIn),
    W.truncations.opList b bIn]
  have prefixEq : (if b = block then (selectedArgs block args.reverse).reverse.map W.cast else []) =
      (entryArguments block args b).map W.cast := by
    by_cases eq : b = block <;> simp [eq, entryArguments, selectedArgs, List.map_reverse]
  rw [prefixEq, List.flatMap_append]
  congr 1
  calc
    _ = ((entryArguments block args b).map W.cast).flatMap (fun op => [op]) := by
      apply List.flatMap_congr_of_mem
      intro op member
      obtain ⟨a, hA, rfl⟩ := List.mem_map.mp member
      obtain ⟨⟨i, width⟩, hi, rfl⟩ := List.mem_map.mp (entryArgument_selected hA).2
      have fresh := (W.truncations.args i width hi).2.2.2.1
      simp only [extensionsBefore]
      rw [List.filter_eq_nil_iff.mpr (by
        intro u hu
        have present := (OpOperandPtr.inBounds_def.mp (slots u hu)).1
        simpa using (show u.operand.op ≠ W.cast ⟨block, i⟩ from fun eq => fresh (eq ▸ present)))]
      rfl
    _ = _ := by simp

/-- Simulate the original operations with their edge extensions, after the entry casts have run. -/
def BodySim : Prop := ∀ (b : BlockPtr) (bIn : b.InBounds src.raw) s t, W.StateRel s t →
  ∀ (targetIn : ∀ op ∈ (b.opList src bIn).flatMap
      (fun op => extensionsBefore W.updates op ++ [op]), op.InBounds dst.raw),
  Sim W.OpRel
    (opListTree ((b.opList src bIn).flatMap (fun op => extensionsBefore W.updates op ++ [op]))
      t targetIn)
    (opListTree (b.opList src bIn) s
      (fun _ h => (BlockPtr.operationListWF src.raw b bIn src.wellFormed).arrayInBounds (by
        simpa [BlockPtr.opList] using h)))

/-- A simulation of each block body extends to a CFG step by setting arguments, interpreting the
entry truncations, and forwarding the return values or next-block arguments. -/
theorem sim_blockStep_of_body (slots : ∀ u ∈ W.updates, u.operand.InBounds src.raw)
    (body : W.BodySim) : W.BlockStepsSim := by
  intro b bIn vs source b' bIn' vt target related
  obtain ⟨rfl, states, sizes, argsRel⟩ := related
  rw [blockStep_entry, blockStep_entry]
  have sameNum := W.ctxSame.numArguments bIn
  by_cases bad : (vs.size != b'.getNumArguments src.raw bIn) = true
  · simp only [bad, ↓reduceIte]
    exact sim_fail _ _
  have sourceSize : vs.size = b'.getNumArguments! src.raw := by
    rw [BlockPtr.getNumArguments!_eq_getNumArguments bIn]
    simpa using bad
  have targetSize : (vt.size != b'.getNumArguments dst.raw bIn') = false := by
    rw [← BlockPtr.getNumArguments!_eq_getNumArguments bIn', sameNum, ← sourceSize, sizes]
    simp
  simp only [bad, targetSize, Bool.false_eq_true, ↓reduceIte]
  cases set : source.variables.setArgumentValues? b' vs bIn with
  | none => exact sim_fail _ _
  | some vars =>
    obtain ⟨outVars, targetSet, prefixResult⟩ := W.enterBlock bIn bIn' states sizes argsRel set
    simp only [targetSet]
    rw [terminatedOpListTree_eq, opListTree_congr (W.operationList slots b' bIn),
      opListTree_append, CTree.bind_assoc, CTree.bind_assoc]
    apply sim_bind_of_returns prefixResult
    rintro ⟨after, _⟩ ⟨rfl, stateRel⟩
    simp only [opListCont, Option.elim_none]
    rw [terminatedOpListTree_eq, CTree.bind_assoc, tree_bind_eq, tree_bind_eq]
    refine Sim.bind _ _ _ _ (body b' bIn _ after stateRel _) ?_
    rintro ⟨t, action'⟩ ⟨s, action⟩ ⟨stateRel', actionRel⟩
    cases action with
    | none => simp
    | some action =>
      cases action' with
      | none => cases action <;> contradiction
      | some action' =>
        simp only [Option.elim_some, pure_bind]
        cases action with
        | «return» values =>
          cases action' with
          | branch => contradiction
          | «return» values' =>
            simp only [finishBlock_return]
            exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inr ⟨stateRel'.1, actionRel⟩)
        | branch values dest =>
          cases action' with
          | «return» => contradiction
          | branch values' dest' =>
            obtain ⟨rfl, vals⟩ := actionRel
            simp only [finishBlock_branch]
            by_cases destIn : dest.InBounds src.raw
            · have destIn' := W.ctxSame.blockIn destIn
              simp only [destIn, destIn', ↓reduceDIte]
              exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inl
                ⟨_, destIn, _, _, _, destIn', _, _, rfl, rfl, rfl, stateRel', vals⟩)
            · simp only [destIn, ↓reduceDIte]
              exact sim_fail _ _

end Veir.Legalization.CTreeProofs.PhiWidening
