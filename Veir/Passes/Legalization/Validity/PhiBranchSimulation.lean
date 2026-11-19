module

public import Veir.Passes.Legalization.Validity.PhiBody
public import Veir.Passes.Legalization.Validity.PhiPlacement
public import Veir.Passes.Legalization.Validity.PhiExtSimulation
public import Veir.Passes.Legalization.Validity.PhiBranches
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Passes.Legalization.Validity.PhiBranches
import all Veir.Passes.Legalization.Validity.PhiBody
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Basic
import all Veir.Interfaces.ControlFlowInterfaces
import all Veir.GlobalOpInfo
import all Veir.IR.OpInfo

public section

namespace Veir.Legalization.CTreeProofs.PhiWidening

open _root_.CTree Veir.CTree

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
  (W : PhiWidening src dst block args)

/-- The inserted extensions prepare the actual target branch operands. Every chosen edge receives
related block arguments, and the operands which decide that edge keep their values. -/
def PreparedPhiBranch (op : OperationPtr) (fixed : Nat) : Prop :=
  ∀ (s : InterpreterState src) (t : InterpreterState dst), W.StateRel s t →
    ∀ srcVals, s.variables.getOperandValues op = some srcVals →
    ∀ extIn : ∀ o ∈ extensionsBefore W.updates op, o.InBounds dst.raw,
    ∃ base, srcVals ⊒ base ∧
      Returns (opListTree (extensionsBefore W.updates op) t extIn) (fun r =>
        r.2 = none ∧ W.StateRel s r.1 ∧ ∃ wide, r.1.variables.getOperandValues op = some wide ∧
        wide.size = base.size ∧ (∀ i < fixed, wide[i]? = base[i]?) ∧
        ∀ edge first last dest, (op.getSuccessors! src.raw)[edge]? = some dest →
          BranchOpInterface.getSuccessorOperands? op edge src.raw = some
            ⟨(op.getOperands! src.raw).extract first last, first⟩ →
          W.ArgsRel dest (base.extract first last) (wide.extract first last))

private theorem extract_value (vs : Array RuntimeValue) (first last i : Nat)
    (hi : i < (vs.extract first last).size) :
    (vs.extract first last)[i]! = vs[first + i]! := by
  have bound := hi
  simp only [Array.size_extract] at bound
  rw [getElem!_pos (vs.extract first last) i hi, Array.getElem_extract,
    getElem!_pos vs (first + i) (by omega)]

/-- The runtime values of every reported edge agree with its static placement of extensions. -/
theorem preparedPhiBranch {op : OperationPtr} (opIn : op.InBounds src.raw) {fixed : Nat}
    (slots : ∀ u ∈ W.updates, u.operand.InBounds src.raw)
    (distinct : (W.updates.map BranchOperandExtension.operand).Nodup)
    (run : widenBlockArgumentsChecked block args src = .ok dst)
    (index : BranchOperandExtension → Nat)
    (links : ∀ u ∈ W.updates, u.operand.op = op →
      LinkedExtension (src := src) (block := block) (args := args) u (index u))
    (placement : W.BranchSlotPlacement op fixed index) : W.PreparedPhiBranch op fixed := by
  intro s t related srcVals read bounds
  obtain ⟨base, refines, returns⟩ :=
    W.returns_extensionsBefore opIn slots distinct run index links related read bounds
  have count := (Array.size_eq_of_mapM_eq_some read).trans refines.1
  refine ⟨base, refines, returns.mono ?_⟩
  rintro ⟨mid, action⟩ ⟨rfl, stateRel, wide, wideRead, h⟩
  refine ⟨rfl, stateRel, wide, wideRead, h.size.symm, ?_, ?_⟩
  · intro i fix
    by_cases inside : i < base.size
    · have wideIn : i < wide.size := h.size ▸ inside
      have same := h.unchanged i inside (by
        intro u hu eq
        have owner := congrArg OpOperandPtr.op eq
        have slot := congrArg OpOperandPtr.index eq
        have lower := placement.fixedPrefix u hu owner
        change u.operand.index = i at slot
        omega)
      simpa [getElem?_pos, getElem!_pos, inside, wideIn] using congrArg some same
    · simp [getElem?_neg, inside, ← h.size]
  · intro edge first last dest hdest hseg
    refine ⟨by simp [Array.size_extract, h.size], fun i hi => ?_⟩
    have wideIn : i < (wide.extract first last).size := by simpa [Array.size_extract, ← h.size] using hi
    have pointerIn : i < ((op.getOperands! src.raw).extract first last).size := by
      simpa [Array.size_extract, count] using hi
    have slotIn : first + i < base.size := by simp only [Array.size_extract] at hi; omega
    rw [extract_value _ _ _ _ hi, extract_value _ _ _ _ wideIn]
    rcases placement.slots edge _ dest hdest hseg i pointerIn with ⟨u, hu, slot, arg⟩ | ⟨untouched, noArg⟩
    · have owner := congrArg OpOperandPtr.op slot
      have idx := congrArg OpOperandPtr.index slot
      change u.operand.index = first + i at idx
      simpa only [arg, idx] using h.widened u hu owner
    · have same := h.unchanged (first + i) slotIn untouched
      rw [ArgumentRel, ite_eq_right noArg, same]
      exact RuntimeValue.isRefinedBy_refl _

private theorem argsRel_of_refined {b : BlockPtr} {vs base wide : Array RuntimeValue}
    (refines : vs ⊒ base) (forwarded : W.ArgsRel b base wide) : W.ArgsRel b vs wide := by
  refine ⟨refines.1.trans forwarded.1, fun i hi => ?_⟩
  have hn : i < base.size := by simpa only [← refines.1] using hi
  have argRel := forwarded.2 i hn
  have hval := refines.2 i hi
  simp only [ArgumentRel] at argRel ⊢
  split at argRel
  next sel =>
    rw [ite_eq_left sel]
    obtain ⟨conf, recovered, h, returns⟩ := argRel
    exact ⟨conf, recovered, RuntimeValue.isRefinedBy_trans hval h, returns⟩
  next no => simpa only [ite_eq_right no] using RuntimeValue.isRefinedBy_trans hval argRel

/-- A touched branch simulates its original instruction once the extension operations have
prepared the operands of each outgoing edge. -/
theorem changedChunkSim {op : OperationPtr} (opIn : op.InBounds src.raw) {fixed : Nat}
    (prep : W.PreparedPhiBranch op fixed)
    (segments : ForwardsBranchSegment (op.getOpType! src.raw)
      (op.getProperties! src.raw (op.getOpType! src.raw)) (op.getSuccessors! src.raw)
      fixed (op.getOperands! src.raw))
    (lifted : (op.getOpType! src.raw).isLifted)
    (monotone : InterpretOp'Monotone (op.getOpType! src.raw)) : W.ChunkSim op opIn := by
  intro s t hst targetIn
  let hdr := W.opHeader opIn
  rw [interpretOperationTree_eq_monadLift s opIn lifted]
  refine sim_monadLift fun ⟨s', act⟩ source => ?_
  obtain ⟨srcVals, srcResults, srcMem, srcVars, hVals, run, hSet, rfl⟩ :=
    interpretOp_some_iff.mp source
  have count : (op.getOperands! src.raw).size = srcVals.size :=
    Array.size_eq_of_mapM_eq_some hVals
  change interpretOp' _ _ _ srcVals _ s.memory = .ok _ at run
  obtain ⟨_, _, _, _, _, _, rfl, rfl, _⟩ := segments srcVals count s.memory _ _ _ _ run
  have zero : op.getNumResults! src.raw = 0 := by
    have typed := (VariableState.setResultValues?_isSome_iff_conforms s.variables opIn).mpr
      ⟨srcVars, hSet⟩
    simpa [OperationPtr.getResultTypes!.size_eq_getNumResults!] using typed.1.symm
  rw [VariableState.setResultValues?_empty zero] at hSet
  cases hSet
  obtain ⟨base, refines, prefixRuns⟩ :=
    prep s t hst srcVals hVals (fun p hp => targetIn p (List.mem_append_left _ hp))
  rw [opListTree_append]
  apply sim_bind_of_returns prefixRuns
  rintro ⟨mid, action⟩ ⟨rfl, stateRel, wide, hWide, hWideSize, controls, afterEdge⟩
  simp only [opListCont, Option.elim_none, opListTree_cons]
  apply sim_tau1_left
  have mono := monotone.monotone (op.getProperties! src.raw (op.getOpType! src.raw))
    (op.getResultTypes! src.raw) srcVals base (op.getSuccessors! src.raw) s.memory mid.memory
    refines stateRel.1
  rw [run, Interp.isRefinedBy_ok_target_iff] at mono
  obtain ⟨⟨out, memory, actBase⟩, baseRun, related⟩ := mono
  obtain ⟨edge, first, last, dest, hDest, hSeg, rfl, rfl, rfl, wideRun⟩ :=
    segments base (count.trans refines.1) mid.memory _ _ _ _ baseRun
  obtain ⟨sourceArgs, srcAct, branchArgs⟩ :
      ∃ a, act = some (.branch a dest) ∧ a ⊒ base.extract first last := by
    obtain ⟨_, _, actRel⟩ := related
    cases act with
    | none => contradiction
    | some c =>
      cases c with
      | «return» => contradiction
      | branch a d =>
        obtain ⟨rfl, h⟩ := actRel
        exact ⟨_, rfl, h⟩
  subst act
  have targetAction : op.interpret dst.raw wide mid.memory =
      .ok (#[], mid.memory, some (.branch (wide.extract first last) dest)) := by
    simp only [OperationPtr.interpret, hdr.properties, hdr.results, hdr.successors]
    rw [hdr.code]
    exact wideRun wide mid.memory hWideSize controls
  have targetZero : op.getNumResults! dst.raw = 0 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hdr.results,
      OperationPtr.getResultTypes!.size_eq_getNumResults!, zero]
  have targetRun : Veir.interpretOp op mid hdr.inBounds =
      .ok (mid, some (.branch (wide.extract first last) dest)) :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hWide).mpr
      ⟨#[], targetAction, VariableState.setResultValues?_empty targetZero⟩
  rw [interpretOperationTree_eq_monadLift mid _ (hdr.code ▸ lifted), targetRun]
  simp only [monadLift, MonadLift.monadLift, pure_bind, Option.elim_some]
  exact (Sim.pure _ _ _).mpr ⟨stateRel, rfl,
    W.argsRel_of_refined branchArgs (afterEdge edge first last dest hDest (by
      unfold BranchOpInterface.getSuccessorOperands?
      dsimp only
      have eq : HasOpInfo.branchOpInterface? (op.getOpType! src.raw) =
        OpCode.branchOpInterface? (op.getOpType! src.raw) := rfl
      rw [eq]
      cases h : OpCode.branchOpInterface? (op.getOpType! src.raw) <;>
        simpa only [h, Option.bind] using hSeg))⟩

end Veir.Legalization.CTreeProofs.PhiWidening
