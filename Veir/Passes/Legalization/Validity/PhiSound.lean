module

public import Veir.Passes.Legalization.Validity.PhiVerifiedRequests
public import Veir.Passes.Legalization.Validity.PhiBranchSimulation
public import Veir.Passes.Legalization.Validity.PhiBranchTransport
public import Veir.Passes.Legalization.Validity.PhiMonotonicity
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.Legalization.Validity.PhiVerifiedRequests
import Veir.Passes.InstructionSelection.Branches.Pass

public section
namespace Veir.Legalization.CTreeProofs
open Puddle.CTree

/-- The facts needed to simulate another block rewrite or the branch-condition widening phase. -/
structure PhiInvariant (ctx : WfIRContext OpCode) : Prop where
  entries : PhiEntries ctx
  segments : PhiSegmentFacts ctx
  forwarding : PhiForwarding ctx
  monotone : TreeMonotoneOps ctx

theorem PhiInvariant.of_verified {ctx : WfIRContext OpCode} {root : OperationPtr}
    (verified : ctx.Verified root) (monotone : TreeMonotoneOps ctx) : PhiInvariant ctx :=
  ⟨.of_verified verified, .of_verified verified, .of_verified verified, monotone⟩

/-- Widening a phi block simulates the original module. Each incoming edge extends exactly
the selected operands. On block entry, each truncation recovers a refinement of the original
argument, for every possible choice of the new high bits. -/
theorem PhiWidening.refines {ctx dst : WfIRContext OpCode} {moduleOp : OperationPtr}
    {block : BlockPtr} {args : List (Nat × Nat)} (W : PhiWidening ctx dst block args)
    (inv : PhiInvariant ctx) (phi : block.hasPredecessor! ctx.raw = true)
    (distinct : (args.map Prod.fst).Nodup) (run : widenBlockArgumentsChecked block args ctx = .ok dst) :
    moduleOp.isModuleRefinedByCTree ctx moduleOp dst := by
  have slots := W.slotsInBounds inv.segments run
  apply W.isModuleRefinedByCTree_of_entries _ inv.entries phi
  apply W.sim_blockStep_of_body slots
  apply W.bodySim_of_chunks
  intro op opIn
  by_cases noUpdates : ∀ u ∈ W.updates, u.operand.op ≠ op
  · exact W.unmodifiedChunk opIn (inv.monotone op opIn)
      noUpdates (W.noUpdates_to_block opIn noUpdates)
  · simp only [Classical.not_forall, Classical.not_not] at noUpdates
    obtain ⟨u, hu, owner⟩ := noUpdates
    obtain ⟨edge, _, seg, read, _, slot⟩ := W.origin hu
    have owner' : edge.op = op := (congrArg OpOperandPtr.op slot).symm.trans owner
    rw [owner'] at read
    have branch := branchInterface_of_segment read
    obtain ⟨forwards, lifted, monotone⟩ := inv.forwarding.semantics op opIn branch
    have placement := W.placement inv.segments run opIn (fun _ _ read =>
      (inv.segments op opIn).fixedLe read)
    exact W.changedChunkSim opIn (W.preparedPhiBranch opIn slots (W.uniqueSlots inv.segments run distinct)
      run W.argumentIndex (fun u hu _ => W.linked inv.segments run u hu) placement) forwards lifted monotone

/-- A single rewrite both refines the module and preserves the hypotheses for the next rewrite. -/
theorem widenBlockArguments_sound {ctx dst : WfIRContext OpCode} {moduleOp : OperationPtr}
    {block : BlockPtr} {args : List (Nat × Nat)} (inv : PhiInvariant ctx)
    (blockIn : block.InBounds ctx.raw) (phi : block.hasPredecessor! ctx.raw = true)
    (distinct : (args.map Prod.fst).Nodup) (run : widenBlockArgumentsChecked block args ctx = .ok dst) :
    moduleOp.isModuleRefinedByCTree ctx moduleOp dst ∧ PhiInvariant dst := by
  obtain ⟨W⟩ := widenBlockArgumentsChecked_frame blockIn distinct run (phiRequestedSlots inv.segments run)
  obtain ⟨segments, forwarding⟩ := W.transportBranchFacts inv.segments inv.forwarding run distinct
  exact ⟨W.refines inv phi distinct run,
    W.preserveEntries inv.entries, segments, forwarding, W.preserveMonotone inv.monotone⟩

theorem widenBlockArguments_refines_of_treeMonotoneOps {ctx dst : WfIRContext OpCode} {moduleOp : OperationPtr}
    {block : BlockPtr} {args : List (Nat × Nat)}
    (verified : ctx.Verified moduleOp) (monotoneOps : TreeMonotoneOps ctx) (blockIn : block.InBounds ctx.raw)
    (phi : block.hasPredecessor! ctx.raw = true) (distinct : (args.map Prod.fst).Nodup)
    (run : widenBlockArgumentsChecked block args ctx = .ok dst) :
    moduleOp.isModuleRefinedByCTree ctx moduleOp dst :=
  (widenBlockArguments_sound (.of_verified verified monotoneOps) blockIn phi distinct run).1

/-- A verified module supplies the operation monotonicity used to simulate unchanged instructions. -/
theorem widenBlockArguments_refines {ctx dst : WfIRContext OpCode} {moduleOp : OperationPtr}
    {block : BlockPtr} {args : List (Nat × Nat)}
    (root : ModuleRoot ctx moduleOp) (blockIn : block.InBounds ctx.raw)
    (phi : block.hasPredecessor! ctx.raw = true) (distinct : (args.map Prod.fst).Nodup)
    (run : widenBlockArgumentsChecked block args ctx = .ok dst) :
    moduleOp.isModuleRefinedByCTree ctx moduleOp dst :=
  widenBlockArguments_refines_of_treeMonotoneOps root.verified (treeMonotoneOps_of_verified root.verified)
    blockIn phi distinct run

end Veir.Legalization.CTreeProofs
