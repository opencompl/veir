module

public import Veir.PatternRewriter.Puddle.Internal.ModuleEligibility
public import Veir.PatternRewriter.Puddle.Internal.CTreeGreedySoundness
public import Veir.PatternRewriter.Puddle.Internal.RewriteWorklistScope
import all Veir.PatternRewriter.Puddle.Internal.CreationStructure
import all Veir.PatternRewriter.Puddle.Internal.WorklistPointerScope
import all Veir.PatternRewriter.Puddle.Internal.RootedAtCheck
import all Veir.IR.Mutators
import all Veir.Rewriter.Basic
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.PatternRewriter.Puddle.Internal.ModuleEligibility
import all Veir.PatternRewriter.Puddle.Internal.CTreeGreedySoundness
import all Veir.PatternRewriter.Puddle.Internal.DriverFunctionStructure
import all Veir.PatternRewriter.Puddle.Internal.DriverStructure
import all Veir.Interfaces.RegionKindInterfaces
import all Veir.IRNesting
import all Veir.IR.Basic

namespace Veir.Puddle
public section

theorem rootEligible_iff {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr}
    (rooted : op.RootedAt moduleOp ctx) :
    rootEligible ctx op = true ↔ CTree.RootAdmissible ctx moduleOp op := by
  cases parent : op.getParentRegion! ctx.raw with
  | none => simp [rootEligible, CTree.RootAdmissible, parent]
  | some region => simp [rootEligible, CTree.RootAdmissible, parent, rooted, and_comm]

/-- Every operation strictly above a region owns at least one region. Its header survives
a regionless rewrite, so each parent edge on the path survives as well. -/
private theorem containerPath_preserved {before after : WfIRContext OpCode}
    (headers : RegionBlockHeadersPreserved before.raw after.raw)
    (owners : ∀ op : OperationPtr, op.InBounds before.raw → 0 < op.getNumRegions! before.raw →
      OperationHeaderPreserved before.raw after.raw op)
    {node root : IRNode} {nodes : List IRNode} (path : IRNode.ParentPath before node root nodes)
    (inside : node.InBounds before.raw)
    (container : ∀ op, node = .operation op → 0 < op.getNumRegions! before.raw) :
    IRNode.ParentPath after node root nodes := by
  induction path with
  | single => exact .single
  | @cons root child parent nodes edge tail ih =>
    have transported : child.parent! after = child.parent! before := by
      cases child with
      | block b => simp [headers.blockParent]
      | region r => simp [headers.regionParent]
      | operation op => simp [(owners op inside (container op rfl)).parent]
    apply IRNode.ParentPath.cons (transported.trans edge)
    apply ih
    · cases child <;> cases parent <;> simp_all [IRNode.parent!, Option.map_eq_some_iff] <;> grind
    · rintro op rfl
      cases child <;> simp only [IRNode.parent!, Option.map_eq_some_iff] at edge <;> try grind
      rename_i region
      obtain ⟨_, parentEq, eq⟩ := edge
      cases eq
      obtain ⟨_, bound, _⟩ := (before.wellFormed.regions region inside).parent_op parentEq
      omega

/-- A regionless rewrite preserves all containers and their parent links. -/
structure ContainerFrame (before after : WfIRContext OpCode) : Prop where
  headers : RegionBlockHeadersPreserved before.raw after.raw
  owners : ∀ op : OperationPtr, op.InBounds before.raw → 0 < op.getNumRegions! before.raw →
    op.InBounds after.raw ∧ OperationHeaderPreserved before.raw after.raw op

/-- Preserve the location of a surviving operation, or of an operation inserted
in the block formerly containing the rewrite root. -/
theorem ContainerFrame.rooted {before after : WfIRContext OpCode} {moduleOp old newOp : OperationPtr}
    (frame : ContainerFrame before after) (detached : moduleOp.getParent! after.raw = none)
    (inside : old.InBounds before.raw) (rooted : old.RootedAt moduleOp before)
    (parent : newOp.getParent! after.raw = old.getParent! before.raw)
    (top : old = moduleOp → newOp = moduleOp) : newOp.RootedAt moduleOp after := by
  obtain ⟨⟨nodes, path⟩, _⟩ := rooted
  cases path with
  | single => exact ⟨by rw [top rfl]; exact .refl, by simp [detached]⟩
  | cons edge tail =>
    simp only [IRNode.parent!_operation, Option.map_eq_some_iff] at edge
    obtain ⟨b, bp, rfl⟩ := edge
    have ancestors := containerPath_preserved frame.headers (fun p h n => (frame.owners p h n).2)
      tail (by grind) (by simp)
    exact ⟨⟨_, .cons (by simp [parent, bp]) ancestors⟩, by simp [detached]⟩

def ContainersPreserved (moduleOp : OperationPtr) (before after : WfIRContext OpCode) : Prop :=
  ∀ op : OperationPtr, op.InBounds before.raw → 0 < op.getNumRegions! before.raw →
    op.RootedAt moduleOp before → op.InBounds after.raw ∧ 0 < op.getNumRegions! after.raw ∧
      op.RootedAt moduleOp after

theorem ContainerFrame.containers {moduleOp : OperationPtr} {before after : WfIRContext OpCode}
    (frame : ContainerFrame before after) (detached : moduleOp.getParent! after.raw = none) :
    ContainersPreserved moduleOp before after := by
  intro op bound hasRegions rooted
  obtain ⟨bound', header⟩ := frame.owners op bound hasRegions
  exact ⟨bound', header.numRegions ▸ hasRegions, frame.rooted detached bound rooted header.parent id⟩

theorem ContainersPreserved.trans {moduleOp : OperationPtr} {a b c : WfIRContext OpCode}
    (first : ContainersPreserved moduleOp a b) (second : ContainersPreserved moduleOp b c) :
    ContainersPreserved moduleOp a c := by
  intro op h n r
  obtain ⟨h, n, r⟩ := first op h n r
  exact second op h n r

/-- Only live candidates can be dispatched. -/
def CandidateInModule (moduleOp : OperationPtr) (ctx : WfIRContext OpCode) (p : OperationPtr) : Prop :=
  p.InBounds ctx.raw → p.RootedAt moduleOp ctx

theorem candidate_operand {ctx : WfIRContext OpCode} {moduleOp p : OperationPtr}
    (verified : ctx.Verified moduleOp) (code : moduleOp.getOpType! ctx.raw = .builtin .module)
    (detached : moduleOp.getParent! ctx.raw = none) (inside : p.InBounds ctx.raw)
    (rooted : p.RootedAt moduleOp ctx) {v : ValuePtr} (mem : v ∈ p.getOperands! ctx.raw) :
    ValueOwnerSatisfies (CandidateInModule moduleOp ctx) v := by
  intro owner eq _
  have rv := (verified.operand_rootedAt_iff code detached inside mem).mpr rooted
  cases v <;> simp_all [ValuePtr.definitionNode]

private theorem InsertBeforeChain.wasInBounds {a b : WfIRContext OpCode}
    (chain : InsertBeforeChain root ops a b) (p : OperationPtr) (h : p.InBounds b.raw) : p.InBounds a.raw := by
  induction chain with
  | nil => exact h
  | cons _ _ _ _ _ ih => have := ih h; grind

private theorem ReplaceResultChain.wasInBounds {a b : WfIRContext OpCode}
    (chain : ReplaceResultChain root vs a b) (p : OperationPtr) (h : p.InBounds b.raw) : p.InBounds a.raw := by
  induction chain with
  | nil => exact h
  | cons _ _ _ _ _ _ ih => have := ih h; grind

theorem eraseOp_survivor {a : WfIRContext OpCode} {root p : OperationPtr} {regions unused inside}
    (h : p.InBounds (WfRewriter.eraseOp a root regions unused inside).raw) :
    p ≠ root ∧ p.InBounds a.raw := by
  have ne : p ≠ root := by
    rintro rfl
    simp only [WfRewriter.eraseOp, Rewriter.eraseOp] at h
    grind [OperationPtr.InBounds, OperationPtr.dealloc]
  exact ⟨ne, (Rewriter.eraseOp_inBounds (.operation p) ne).mp h⟩

theorem Pattern.splice_preserves_scope (rule : Pattern OpCode)
    {rw result : PatternRewriter OpCode} {op moduleOp : OperationPtr} {opIn : op.InBounds rw.ctx.raw}
    {created : WfIRContext OpCode} {ops : Array OperationPtr} {values : Array ValuePtr}
    (localRun : rule.interpret rw.ctx op = some (created, some (ops, values)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rw op opIn = some result)
    (attached : (op.getParent! rw.ctx.raw).isSome) (regionless : op.getNumRegions! rw.ctx.raw = 0)
    (rooted : op.RootedAt moduleOp rw.ctx) (detached : moduleOp.getParent! result.ctx.raw = none)
    (verified : rw.ctx.Verified moduleOp) (code : moduleOp.getOpType! rw.ctx.raw = .builtin .module)
    (all : rw.worklist.All (CandidateInModule moduleOp rw.ctx)) :
    ContainersPreserved moduleOp rw.ctx result.ctx ∧ result.worklist.All (CandidateInModule moduleOp result.ctx) := by
  have noParent : moduleOp.getParent! rw.ctx.raw = none := by simpa using rooted.2
  have notOwn := fromLocalRewrite_result_notOwn_indexed localRun run
  have frame : ContainerFrame rw.ctx result.ctx := by
    refine ⟨rule.fromLocalRewrite_regionBlockHeaders localRun run attached regionless notOwn, ?_⟩
    intro p bound n
    have ne : p ≠ op := by rintro rfl; omega
    exact ⟨rule.fromLocalRewrite_existing_inBounds localRun run attached regionless notOwn p bound ne,
      (rule.fromLocalRewrite_existing_frame localRun run attached regionless notOwn p bound ne).1⟩
  have queued := rule.fromLocalRewrite_worklist localRun run attached regionless all (fun _ => rooted)
    (fun p h ok _ mem => candidate_operand verified code noParent h (ok h) mem)
    (fun p h i mem _ => (verified.operand_rootedAt_iff code noParent h mem).mp rooted)
    (fun _ missing bound => (missing bound).elim)
  refine ⟨frame.containers detached, queued.mono ?_⟩
  intro p prior bound
  obtain ⟨inserted, replaced, ins, sub, rin, n, u⟩ := rule.fromLocalRewrite_safe_phases localRun run attached regionless notOwn
  have eq := fromLocalRewrite_ctx localRun run
  rw [driverContext_eq_of_chains ins sub rin n u] at eq
  obtain ⟨ne, prev⟩ := eraseOp_survivor (eq ▸ bound)
  by_cases old : p.InBounds rw.ctx.raw
  · exact frame.rooted detached old (prior old)
      (rule.fromLocalRewrite_existing_frame localRun run attached regionless notOwn p old ne).1.parent id
  · have member := ((rule.interpret_structure localRun).1 p).mpr
          ⟨ins.wasInBounds p (sub.wasInBounds p prev), old⟩
    apply frame.rooted detached opIn rooted
      ((rule.fromLocalRewrite_inserted_splice localRun run attached regionless notOwn).2 p member)
    rintro rfl
    simp [noParent] at attached

end
end Veir.Puddle
