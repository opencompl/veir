module

public import Veir.Passes.Legalization.Validity.PhiIncoming
public import Veir.Passes.Legalization.Validity.PhiEdges
public import Veir.Passes.Legalization.Validity.PhiFrame
public import Veir.Passes.Legalization.Validity.PhiSimulation

import all Veir.IR.Basic
import all Veir.Passes.Legalization.Validity.PhiFrame
import all Veir.IR.InBounds
import all Veir.Passes.InstructionSelection.Branches.Pass

public section
namespace Veir.Legalization.CTreeProofs

/-- The truncations at block entry and the extensions on all incoming edges of a phi widening. -/
structure PhiWidening (src dst : WfIRContext OpCode) (block : BlockPtr) (args : List (Nat × Nat)) where
  truncated : WfIRContext OpCode
  cast : BlockArgumentPtr → OperationPtr
  truncations : WidenArgumentsFrame src truncated block args.reverse cast
  uses : Array BlockOperandPtr
  chain : block.DefUse src.raw uses
  edges : List (OperationPtr × SuccessorOperands)
  segments : uses.toList.mapM (fun e => do
      return (e.op, ← BranchOpInterface.getSuccessorOperands? e.op e.index src.raw)) = some edges
  updates : List BranchOperandExtension
  extensions : WidenedIncomingEdges truncated dst updates
  requests : updates.map (fun u => (u.operand, u.width)) =
    edges.flatMap (fun e => branchOperandRequests e.1 e.2 args)

/-- Build the two frames from the successful run, using the bounds of the original forwarded slots. -/
theorem widenBlockArgumentsChecked_frame {src dst : WfIRContext OpCode} {block : BlockPtr}
    {args : List (Nat × Nat)} (blockIn : block.InBounds src.raw)
    (distinct : (args.map Prod.fst).Nodup)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (slots : ∀ (uses : Array BlockOperandPtr) (edges : List (OperationPtr × SuccessorOperands)),
      block.DefUse src.raw uses →
      uses.toList.mapM (fun e => do
        return (e.op, ← BranchOpInterface.getSuccessorOperands? e.op e.index src.raw)) = some edges →
      ∀ x ∈ edges.flatMap (fun e => branchOperandRequests e.1 e.2 args), x.1.InBounds src.raw) :
    Nonempty (PhiWidening src dst block args) := by
  obtain ⟨uses, edges, truncated, chain, segments, entryRun, edgeRun⟩ :=
    widenBlockArgumentsChecked_steps blockIn run
  have argBounds : ∀ i ∈ args.map Prod.fst, (⟨block, i⟩ : BlockArgumentPtr).InBounds src.raw := by
    intro i member
    obtain ⟨⟨i, width⟩, selected, rfl⟩ := List.mem_map.mp member
    exact BlockArgumentPtr.inBounds_def.mpr ⟨blockIn,
      by simpa [← BlockPtr.getNumArguments!_eq_getNumArguments blockIn] using
        (widenBlockArgumentsChecked_argumentType run selected).1⟩
  obtain ⟨cast, truncs⟩ := widenBlockArgument_fold_spec argBounds distinct entryRun
  have validSlots := slots uses edges chain segments
  obtain ⟨updates, exts, requests⟩ := widenIncomingEdges_frame edges args (fun x hx => by
    obtain ⟨opIn, indexIn⟩ := OpOperandPtr.inBounds_def.mp (validSlots x hx)
    have opSame := truncs.ops x.1.op opIn
    apply OpOperandPtr.inBounds_def.mpr
    refine ⟨opSame.inBounds, ?_⟩
    rwa [← OperationPtr.getNumOperands!_eq_getNumOperands opSame.inBounds, ← OperationPtr.getOperands!.size_eq_getNumOperands!, opSame.operands, Array.size_map,
      OperationPtr.getOperands!.size_eq_getNumOperands!, OperationPtr.getNumOperands!_eq_getNumOperands opIn]) edgeRun
  exact ⟨⟨truncated, cast, truncs, uses, chain, edges, segments, updates, exts, requests⟩⟩

namespace PhiWidening

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

include W in
theorem ctxSame : CtxSame src.raw dst.raw := W.truncations.ctxSame.trans W.extensions.ctxSame

include W in
theorem opHeader {op : OperationPtr} (hin : op.InBounds src.raw) : PhiOpHeader src dst op :=
  let entry := W.truncations.ops op hin
  (PhiOpHeader.of_same entry).trans (W.extensions.opHeader entry.inBounds)

def mapValue : ValuePtr → ValuePtr := lowerArgs (selectedArgs block args.reverse) W.cast

theorem mappedInBounds {value : ValuePtr} (valueIn : value.InBounds src.raw) :
    (W.mapValue value).InBounds dst.raw := by
  apply W.extensions.bounds (.value _)
  cases value with
  | opResult r => exact W.truncations.bounds _ valueIn
  | blockArgument a =>
    simp only [mapValue, lowerArgs]
    split
    next member =>
      obtain ⟨⟨i, width⟩, hi, rfl⟩ := List.mem_map.mp member
      obtain ⟨_, _, castIn, _, _, types, _⟩ := W.truncations.args i width hi
      have one := congrArg Array.size types
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, List.size_toArray,
        List.length_cons, List.length_nil] at one
      simpa using OperationPtr.getResult_inBounds _ castIn 0 (by grind)
    next => exact W.truncations.bounds _ valueIn

theorem castInj {a b : BlockArgumentPtr}
    (ha : a ∈ selectedArgs block args.reverse) (hb : b ∈ selectedArgs block args.reverse)
    (same : W.cast a = W.cast b) : a = b := by
  obtain ⟨⟨i, wi⟩, hi, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨j, wj⟩, hj, rfl⟩ := List.mem_map.mp hb
  obtain ⟨_, _, _, _, _, _, operandsI, _⟩ := W.truncations.args i wi hi
  obtain ⟨_, _, _, _, _, _, operandsJ, _⟩ := W.truncations.args j wj hj
  rw [same] at operandsI
  simpa using operandsI.symm.trans operandsJ

theorem mapped_eq_castResult {v : ValuePtr} (vin : v.InBounds src.raw) {a : BlockArgumentPtr}
    (ha : a ∈ selectedArgs block args.reverse) :
    W.mapValue v = (W.cast a).getResult 0 → v = .blockArgument a := by
  cases v with
  | opResult v =>
    obtain ⟨⟨i, wi⟩, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, _, fresh, _⟩ := W.truncations.args i wi hi
    intro eq
    have owner := congrArg OpResultPtr.op (ValuePtr.opResult.inj eq)
    change v.op = W.cast ⟨block, i⟩ at owner
    exact (fresh (owner ▸ (OpResultPtr.inBounds_def.mp (show v.InBounds src.raw by simpa using vin)).1)).elim
  | blockArgument b =>
    simp only [mapValue, lowerArgs]
    split
    next hb =>
      intro eq
      have same := congrArg OpResultPtr.op (ValuePtr.opResult.inj eq)
      exact congrArg ValuePtr.blockArgument (W.castInj hb ha same)
    next => simp

theorem mappedType {v : ValuePtr} (vin : v.InBounds src.raw) :
    (W.mapValue v).getType! dst.raw = v.getType! src.raw := by
  cases v with
  | opResult r =>
    exact (W.extensions.valueTypes _ (W.truncations.bounds _ vin)).trans
      (W.truncations.otherTypes _ vin (by simp))
  | blockArgument a =>
    simp only [mapValue, lowerArgs]
    split
    next member =>
      obtain ⟨⟨i, width⟩, hi, rfl⟩ := List.mem_map.mp member
      obtain ⟨_, _, castIn, _, _, types, _⟩ := W.truncations.args i width hi
      have one := congrArg Array.size types
      have resultIn := OperationPtr.getResult_inBounds _ castIn 0 (by grind)
      rw [W.extensions.valueTypes _ (by simpa using resultIn), ValuePtr.getType!_opResult]
      rw [← OperationPtr.getResultTypes!.getElem!_eq (by grind)]
      simp [types]
    next no =>
      exact (W.extensions.valueTypes _ (W.truncations.bounds _ vin)).trans
        (W.truncations.otherTypes _ vin (fun _ member eq => no (ValuePtr.blockArgument.inj eq ▸ member)))

def mapping : ValueMapping src dst := fun ⟨v, vin⟩ => ⟨W.mapValue v, W.mappedInBounds vin⟩

abbrev StateRel (source : InterpreterState src) (target : InterpreterState dst) : Prop :=
  source.RefinedUnder (· ⊒ ·) target W.mapping

/-- At entry to a widened argument, the incoming value fits its new type and the truncation
binds a refinement of the source value. Other arguments follow ordinary value refinement. -/
def ArgumentRel (a : BlockArgumentPtr) (source target : RuntimeValue) : Prop :=
  if a ∈ selectedArgs block args.reverse then
    target.Conforms ((ValuePtr.blockArgument a).getType! dst.raw) ∧
    ∃ restored, source ⊒ restored ∧ ∃ castIn : (W.cast a).InBounds dst.raw,
      ∀ entered : InterpreterState dst, entered.variables.getVar? (.blockArgument a) = some target →
      Veir.CTree.Returns (Veir.CTree.interpretOperationTree (W.cast a) entered castIn)
        (SetsCastResult (W.cast a) entered restored)
  else source ⊒ target

def ArgsRel (b : BlockPtr) (vs vs' : Array RuntimeValue) : Prop :=
  vs.size = vs'.size ∧ ∀ i < vs.size, W.ArgumentRel (b.getArgument i) vs[i]! vs'[i]!

def CallRel : BlockCallRel src dst := fun b vs s b' vs' s' =>
  b' = b ∧ W.StateRel s s' ∧ W.ArgsRel b vs vs'

def ActionRel : Option ControlFlowAction → Option ControlFlowAction → Prop
  | none, none => True
  | some (.return vs), some (.return vs') => vs ⊒ vs'
  | some (.branch vs b), some (.branch vs' b') => b = b' ∧ W.ArgsRel b vs vs'
  | _, _ => False

abbrev OpRel (t : InterpreterState dst × Option ControlFlowAction)
    (s : InterpreterState src × Option ControlFlowAction) : Prop :=
  W.StateRel s.1 t.1 ∧ W.ActionRel s.2 t.2

end PhiWidening

end Veir.Legalization.CTreeProofs
