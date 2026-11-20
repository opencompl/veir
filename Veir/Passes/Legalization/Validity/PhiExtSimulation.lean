module

public import Veir.Passes.Legalization.Validity.PhiWidening

import all Veir.Passes.Legalization.Validity.PhiEdges
import all Veir.Passes.Legalization.Validity.PhiSimulation
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.InstructionSelection.Branches.Pass
import all Veir.IR.Basic
import all Veir.IR.Attribute
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas

public section
namespace Veir.Legalization.CTreeProofs.PhiWidening

open _root_.CTree Veir.CTree

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

private theorem inTruncated {v : ValuePtr} (vin : v.InBounds src.raw) :
    (W.mapValue v).InBounds W.truncated.raw := by
  cases v with
  | opResult r => exact W.truncations.bounds _ vin
  | blockArgument a =>
    simp only [mapValue, lowerArgs]
    split
    next selected =>
      obtain ⟨⟨i, w⟩, mem, rfl⟩ := List.mem_map.mp selected
      obtain ⟨_, _, castIn, _, _, types, _⟩ := W.truncations.args i w mem
      rw [ValuePtr.inBounds_opResult]
      exact OperationPtr.getResult_inBounds _ castIn 0 (by
        have len := congrArg Array.size types
        grind)
    next => exact W.truncations.bounds _ vin

/-- The old SSA values are represented by values from the intermediate context, so writing
a fresh extension result preserves all of their bindings. -/
theorem mapValue_ne_extension {u : BranchOperandExtension} (hu : u ∈ W.updates)
    {v : ValuePtr} (vin : v.InBounds src.raw) :
    W.mapValue v ≠ (u.ext.getResult 0 : ValuePtr) := by
  intro eq
  have fresh := W.extensions.fresh hu
  have bound := W.inTruncated vin
  rw [eq, ValuePtr.inBounds_opResult] at bound
  exact fresh (OpResultPtr.inBounds_def.mp bound).1

private theorem slotInTruncated {p : OpOperandPtr} (pin : p.InBounds src.raw) :
    p.InBounds W.truncated.raw := by
  obtain ⟨opIn, index⟩ := OpOperandPtr.inBounds_def.mp pin
  have same := W.truncations.ops p.op opIn
  refine OpOperandPtr.inBounds_def.mpr ⟨same.inBounds, ?_⟩
  rwa [← OperationPtr.getNumOperands!_eq_getNumOperands same.inBounds,
    ← OperationPtr.getOperands!.size_eq_getNumOperands!, same.operands, Array.size_map,
    OperationPtr.getOperands!.size_eq_getNumOperands!, OperationPtr.getNumOperands!_eq_getNumOperands opIn]

private theorem slotValueIn {p : OpOperandPtr} (pin : p.InBounds src.raw) :
    (p.op.getOperand! src.raw p.index).InBounds src.raw := by
  obtain ⟨opIn, index⟩ := OpOperandPtr.inBounds_def.mp pin
  exact OperationPtr.getOperands!_inBounds src.wellFormed.inBounds opIn
    (OperationPtr.getOperands!.mem_iff_exists_index.mpr ⟨p.index, by
      simpa [OperationPtr.getNumOperands!_eq_getNumOperands opIn] using index, rfl⟩)

private theorem slotValueTruncated {p : OpOperandPtr} (pin : p.InBounds src.raw) :
    p.op.getOperand! W.truncated.raw p.index = W.mapValue (p.op.getOperand! src.raw p.index) := by
  obtain ⟨opIn, index⟩ := OpOperandPtr.inBounds_def.mp pin
  have same := W.truncations.ops p.op opIn
  have valid : p.index < (p.op.getOperands! src.raw).size := by
    simpa [OperationPtr.getNumOperands!_eq_getNumOperands opIn] using index
  rw [← OperationPtr.getOperands!.getElem!_eq_getOperand!, same.operands,
    getElem!_pos _ _ (by simpa using valid), Array.getElem_map,
    OperationPtr.getOperands!.getElem_eq_getOperand!]
  rfl

/-- Recover the source operand of an extension and the destination argument it widens. -/
def LinkedExtension (u : BranchOperandExtension) (i : Nat) : Prop :=
  (i, u.width) ∈ args ∧ (u.operand.op.getOperand! src.raw u.operand.index).getType! src.raw =
    (block.getArgument i).getType! src.raw

private theorem returns_extension {u : BranchOperandExtension} (hu : u ∈ W.updates) {i : Nat}
    (slots : ∀ v ∈ W.updates, v.operand.InBounds src.raw)
    (distinct : (W.updates.map BranchOperandExtension.operand).Nodup)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (link : LinkedExtension (src := src) (args := args) (block := block) u i)
    {target : InterpreterState dst} {base : RuntimeValue}
    (lookup : target.variables.getVar? (W.mapValue (u.operand.op.getOperand! src.raw u.operand.index)) = some base) :
    ∃ extIn : u.ext.InBounds dst.raw, Returns (interpretOperationTree u.ext target extIn)
      (fun r => ∃ tv, SetsCastResult u.ext target tv r ∧ W.ArgumentRel (block.getArgument i) base tv) := by
  obtain ⟨chosen, operandType⟩ := link
  have member := List.mem_reverse.mpr chosen
  have selected : block.getArgument i ∈ selectedArgs block args.reverse :=
    List.mem_map.mpr ⟨(i, u.width), member, rfl⟩
  obtain ⟨_, extIn, extCode, extTypes, extOperands, _⟩ := W.extensions.extension
    (fun u h => W.slotInTruncated (slots u h)) distinct u hu
  rw [W.slotValueTruncated (slots u hu)] at extOperands
  obtain ⟨_, bits, narrow, _, width⟩ := widenBlockArgumentsChecked_argumentType run chosen
  obtain ⟨argIn, wide, castIn, castFresh, castCode, castType, castOperands, castProp, _⟩ :=
    W.truncations.args i u.width member
  have castSame := W.extensions.opSame castIn (fun v hv eq =>
    castFresh (eq ▸ (OpOperandPtr.inBounds_def.mp (slots v hv)).1))
  have vin := slotValueIn (slots u hu)
  have fits := VariableState.getVar?_conforms lookup
  rw [W.mappedType vin, operandType, narrow] at fits
  obtain ⟨n, rfl⟩ := RuntimeValue.Conforms.integerType.mp fits
  have typeEq : (ValuePtr.blockArgument (block.getArgument i)).getType! src.raw =
      (IntegerType.signless bits : TypeAttr) := by simpa using narrow
  have castTypes : (W.cast (block.getArgument i)).getResultTypes! dst.raw = #[(IntegerType.signless bits : TypeAttr)] :=
    castSame.resultTypes.trans (castType.trans (congrArg (fun t : TypeAttr => #[t]) typeEq))
  have castArgs : (W.cast (block.getArgument i)).getOperands! dst.raw = #[.blockArgument (block.getArgument i)] := by
    simp only [BlockPtr.getArgument_def]; rw [castSame.operands, castOperands]; simp
  have one := returns_widenedArgumentOperations (narrow := IntegerType.signless bits) width
    extIn extCode extTypes extOperands castSame.inBounds (castSame.opType.trans castCode) castTypes
    ((castSame.properties _).trans castProp) castArgs target lookup
  have argType := (W.extensions.valueTypes _ (W.truncations.bounds _ (by simpa using argIn))).trans wide
  refine ⟨extIn, one.mono ?_⟩
  rintro r ⟨w, writes, restore⟩
  refine ⟨_, writes, ?_⟩
  rw [ArgumentRel, ite_eq_left selected, BlockPtr.getArgument_def, argType]
  exact ⟨by simp [IntegerType.signless], _, RuntimeValue.isRefinedBy_refl _, castSame.inBounds, restore⟩

/-- The branch receives the original values at untouched slots and successfully extended
values at exactly the slots that carry widened arguments. -/
structure BranchOperandsRel (op : OperationPtr) (index : BranchOperandExtension → Nat)
    (base wide : Array RuntimeValue) : Prop where
  size : base.size = wide.size
  unchanged : ∀ j < base.size, (∀ u ∈ W.updates, u.operand ≠ ⟨op, j⟩) → wide[j]! = base[j]!
  widened : ∀ u ∈ W.updates, u.operand.op = op → W.ArgumentRel (block.getArgument (index u))
    base[u.operand.index]! wide[u.operand.index]!

private theorem returns_extensionList {target : InterpreterState dst}
    (pending : List BranchOperandExtension) (index : BranchOperandExtension → Nat)
    (base : Array RuntimeValue) (slots : ∀ u ∈ W.updates, u.operand.InBounds src.raw)
    (distinct : (W.updates.map BranchOperandExtension.operand).Nodup)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (members : ∀ u ∈ pending, u ∈ W.updates)
    (links : ∀ u ∈ pending, LinkedExtension (src := src) (args := args) (block := block) u (index u))
    (unique : (pending.map BranchOperandExtension.ext).Nodup)
    (reads : ∀ u ∈ pending, target.variables.getVar? (W.mapValue
      (u.operand.op.getOperand! src.raw u.operand.index)) = some base[u.operand.index]!)
    (bounds : ∀ o ∈ pending.map BranchOperandExtension.ext, o.InBounds dst.raw) :
    Returns (opListTree (pending.map BranchOperandExtension.ext) target bounds) (fun r =>
      r.2 = none ∧ r.1.memory = target.memory ∧
      (∀ v : ValuePtr, (∀ u ∈ pending, v ≠ u.ext.getResult 0) →
        r.1.variables.getVar? v = target.variables.getVar? v) ∧
      ∀ u ∈ pending, ∃ t, r.1.variables.getVar? (u.ext.getResult 0) = some t ∧
        W.ArgumentRel (block.getArgument (index u)) base[u.operand.index]! t) := by
  induction pending generalizing target with
  | nil => simp
  | cons u tail ih =>
    have hu := members u List.mem_cons_self
    obtain ⟨_, one⟩ := W.returns_extension hu slots distinct run (links u List.mem_cons_self)
      (reads u List.mem_cons_self)
    simp only [List.map_cons, opListTree_cons, returns_tau1]
    apply one.bind
    rintro ⟨after, action⟩ ⟨wide, ⟨rfl, mem, vars⟩, rel⟩
    simp only [Option.elim_none]
    obtain ⟨newExt, tailUnique⟩ := List.nodup_cons.mp unique
    have tailReads : ∀ v ∈ tail, after.variables.getVar? (W.mapValue
        (v.operand.op.getOperand! src.raw v.operand.index)) = some base[v.operand.index]! := by
      intro v hv
      have present := members v (List.mem_cons_of_mem _ hv)
      rw [vars, ite_eq_right (W.mapValue_ne_extension hu (slotValueIn (slots _ present)))]
      exact reads v (List.mem_cons_of_mem _ hv)
    apply (ih (target := after) (fun v hv => members v (List.mem_cons_of_mem _ hv))
      (fun v hv => links v (List.mem_cons_of_mem _ hv)) tailUnique tailReads _).mono
    rintro ⟨final, action⟩ ⟨rfl, memTail, keeps, writes⟩
    refine ⟨rfl, memTail.trans mem, ?_, ?_⟩
    · intro v h
      rw [keeps v (fun w hw => h w (List.mem_cons_of_mem _ hw)), vars,
        ite_eq_right (h u List.mem_cons_self)]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | later
      · refine ⟨wide, ?_, rel⟩
        rw [keeps, vars, ite_eq_left rfl]
        intro w hw eq
        have same : v.ext = w.ext := congrArg OpResultPtr.op (ValuePtr.opResult.inj eq)
        exact newExt (same ▸ List.mem_map_of_mem hw)
      · exact writes v later

private theorem baseOperands {op : OperationPtr} (opIn : op.InBounds src.raw)
    {source : InterpreterState src} {target : InterpreterState dst} (states : W.StateRel source target)
    {vs : Array RuntimeValue} (read : source.variables.getOperandValues op = some vs) :
    ∃ base : Array RuntimeValue, vs ⊒ base ∧ ∀ i < op.getNumOperands! src.raw,
      target.variables.getVar? (W.mapValue (op.getOperand! src.raw i)) = some base[i]! := by
  obtain ⟨size, lookups⟩ := VariableState.getOperandValues_eq_some_iff.mp read
  have atIndex (i : Fin vs.size) : ∃ tv,
      target.variables.getVar? (W.mapValue (op.getOperand! src.raw i)) = some tv ∧ vs[i]! ⊒ tv := by
    have valid : i.val < op.getNumOperands! src.raw := by omega
    have vin := OperationPtr.getOperands!_inBounds src.wellFormed.inBounds opIn
      (OperationPtr.getOperands!.mem_iff_exists_index.mpr ⟨i, valid, rfl⟩)
    exact states.2 _ vin _ (lookups i valid)
  classical
  let base := Array.ofFn (fun i : Fin vs.size => (atIndex i).choose)
  have get (i : Nat) (h : i < vs.size) : base[i]! = (atIndex ⟨i, h⟩).choose := by
    rw [getElem!_pos base i (by simpa [base] using h)]
    exact Array.getElem_ofFn (f := fun i : Fin vs.size => (atIndex i).choose) _
  refine ⟨base, ⟨by simp [base], fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [get i hi]
    exact (atIndex ⟨i, hi⟩).choose_spec.2
  · have bound : i < vs.size := by omega
    rw [get i bound]
    exact (atIndex ⟨i, bound⟩).choose_spec.1

/-- Execute the extensions immediately before a branch. The original source operands refine
the values in the target before extension. The branch then sees exactly those values at the
untouched slots, and the related widened value at every rewritten slot. -/
theorem returns_extensionsBefore {op : OperationPtr} (opIn : op.InBounds src.raw)
    (slots : ∀ u ∈ W.updates, u.operand.InBounds src.raw)
    (distinct : (W.updates.map BranchOperandExtension.operand).Nodup)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (index : BranchOperandExtension → Nat)
    (links : ∀ u ∈ W.updates, u.operand.op = op →
      LinkedExtension (src := src) (block := block) (args := args) u (index u))
    {source : InterpreterState src} {target : InterpreterState dst} (related : W.StateRel source target)
    {vs : Array RuntimeValue} (read : source.variables.getOperandValues op = some vs)
    (bounds : ∀ o ∈ extensionsBefore W.updates op, o.InBounds dst.raw) :
    ∃ base : Array RuntimeValue, vs ⊒ base ∧
      Returns (opListTree (extensionsBefore W.updates op) target bounds) (fun r =>
        r.2 = none ∧ W.StateRel source r.1 ∧ ∃ wide,
          r.1.variables.getOperandValues op = some wide ∧ W.BranchOperandsRel op index base wide) := by
  obtain ⟨base, refines, baseRead⟩ := W.baseOperands opIn related read
  refine ⟨base, refines, ?_⟩
  let pending := W.updates.filter (fun u => u.operand.op == op)
  have filtered (u : BranchOperandExtension) :
      u ∈ pending ↔ u ∈ W.updates ∧ u.operand.op = op := by simp [pending]
  have unique : (pending.map BranchOperandExtension.ext).Nodup :=
    W.extensions.freshExtensions.sublist ((List.filter_sublist ..).map _)
  have sourceSize := (VariableState.getOperandValues_eq_some_iff.mp read).1
  have baseSize : op.getNumOperands! src.raw = base.size := sourceSize.trans refines.1
  have step := W.truncations.ops op opIn
  have sameNum : op.getNumOperands! dst.raw = op.getNumOperands! src.raw := by
    rw [W.extensions.numOperands step.inBounds, ← OperationPtr.getOperands!.size_eq_getNumOperands!,
      step.operands, Array.size_map, OperationPtr.getOperands!.size_eq_getNumOperands!]
  have middleSlots : ∀ u ∈ W.updates, u.operand.InBounds W.truncated.raw :=
    fun u h => W.slotInTruncated (slots u h)
  apply (W.returns_extensionList (target := target) pending index base slots distinct run
    (fun u h => ((filtered u).mp h).1)
    (fun u h => links u ((filtered u).mp h).1 ((filtered u).mp h).2) unique (fun u h => ?_)
    bounds).mono
  · rintro ⟨after, action⟩ ⟨rfl, mem, keeps, writes⟩
    refine ⟨rfl, ⟨mem ▸ related.1, fun v vin sv hv => ?_⟩, ?_⟩
    · obtain ⟨tv, old, rel⟩ := related.2 v vin sv hv
      refine ⟨tv, ?_, rel⟩
      change after.variables.getVar? (W.mapValue v) = some tv
      rw [keeps _ (fun u hu => W.mapValue_ne_extension ((filtered u).mp hu).1 vin)]
      exact old
    · have changed (u : BranchOperandExtension) (hu : u ∈ W.updates) (owner : u.operand.op = op) :
          ∃ tv, after.variables.getVar? (op.getOperand! dst.raw u.operand.index) = some tv ∧
            W.ArgumentRel (block.getArgument (index u)) base[u.operand.index]! tv := by
        have pointer := (W.extensions.extension middleSlots distinct u hu).2.2.2.2.2
        rw [← owner, pointer]
        exact writes u ((filtered u).mpr ⟨hu, owner⟩)
      have unchanged (j : Nat) (hj : j < base.size)
          (no : ∀ u ∈ W.updates, u.operand ≠ ⟨op, j⟩) :
          after.variables.getVar? (op.getOperand! dst.raw j) = some base[j]! := by
        let slot : OpOperandPtr := ⟨op, j⟩
        have valid : slot.InBounds src.raw := OpOperandPtr.inBounds_def.mpr ⟨opIn, by
          change j < op.getNumOperands src.raw opIn
          rw [← OperationPtr.getNumOperands!_eq_getNumOperands opIn, baseSize]
          exact hj⟩
        have untouched := W.extensions.untouchedOperand (W.slotInTruncated valid)
          (fun u hu => Ne.symm (no u hu))
        change after.variables.getVar? (slot.op.getOperand! dst.raw slot.index) = _
        rw [untouched, W.slotValueTruncated valid, keeps _ (fun u hu =>
          W.mapValue_ne_extension ((filtered u).mp hu).1 (slotValueIn valid))]
        exact baseRead j (baseSize ▸ hj)
      have available : ∃ wide, after.variables.getOperandValues op = some wide := by
        unfold VariableState.getOperandValues
        apply Array.exists_mapM_option_eq_some_iff.mpr
        intro j hj
        rw [OperationPtr.getOperands!.getElem_eq_getOperand!]
        have size : j < base.size := by
          rwa [OperationPtr.getOperands!.size_eq_getNumOperands!, sameNum, baseSize] at hj
        by_cases has : ∃ u ∈ W.updates, u.operand = ⟨op, j⟩
        · obtain ⟨u, hu, eq⟩ := has
          obtain ⟨tv, lookup, _⟩ := changed u hu (congrArg OpOperandPtr.op eq)
          have idx : u.operand.index = j := congrArg OpOperandPtr.index eq
          exact ⟨tv, idx ▸ lookup⟩
        · exact ⟨_, unchanged j size (fun u hu eq => has ⟨u, hu, eq⟩)⟩
      obtain ⟨wide, finalRead⟩ := available
      obtain ⟨wideSize, lookups⟩ := VariableState.getOperandValues_eq_some_iff.mp finalRead
      refine ⟨wide, finalRead, (baseSize.symm.trans sameNum.symm).trans wideSize,
        fun j hj no => ?_, fun u hu owner => ?_⟩
      · exact Option.some.inj ((lookups j (by omega)).symm.trans (unchanged j hj no))
      · obtain ⟨v, lookup, rel⟩ := changed u hu owner
        obtain ⟨branchIn, slotIn⟩ := OpOperandPtr.inBounds_def.mp (slots u hu)
        have valid : u.operand.index < op.getNumOperands! dst.raw := by
          rw [sameNum, ← owner, OperationPtr.getNumOperands!_eq_getNumOperands branchIn]
          exact slotIn
        rw [lookups _ valid] at lookup
        exact Option.some.inj lookup ▸ rel
  · obtain ⟨member, owner⟩ := (filtered u).mp h
    obtain ⟨branchIn, bound⟩ := OpOperandPtr.inBounds_def.mp (slots u member)
    rw [owner]
    apply baseRead
    rwa [← owner, OperationPtr.getNumOperands!_eq_getNumOperands branchIn]

end Veir.Legalization.CTreeProofs.PhiWidening
