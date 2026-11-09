module

public import Veir.PatternRewriter.Puddle.Internal.ScopedWorklist
public import Veir.PatternRewriter.Puddle.Internal.WorklistPointerScope
public import Veir.PatternRewriter.Puddle.Internal.DriverFunctionStructure
public import Veir.Verifier
import all Veir.PatternRewriter.Puddle.Internal.DriverStructure
import all Veir.PatternRewriter.Puddle.Internal.CreationStructure
import all Veir.PatternRewriter.Puddle.Internal.WorklistPointerScope
import all Veir.PatternRewriter.Basic
import all Veir.IR.Basic
import all Veir.IRNesting

public section
namespace Veir.Puddle

/-- The two sets of neighbors that the local rewrite driver may enqueue. -/
private structure WorklistNeighbors (ctx : WfIRContext OpCode) (root : OperationPtr)
    (P : OperationPtr → Prop) : Prop where
  defs : ∀ v ∈ root.getOperands! ctx.raw, ValueOwnerSatisfies P v
  users : ∀ op, op.InBounds ctx.raw → ∀ i, (root.getResult i : ValuePtr) ∈ op.getOperands! ctx.raw → P op

private theorem WorklistNeighbors.replace {ctx : WfIRContext OpCode} {root : OperationPtr}
    {v : ValuePtr} {i : Nat} (different : (root.getResult i : ValuePtr) ≠ v)
    (oldIn : (root.getResult i : ValuePtr).InBounds ctx.raw) (newIn : v.InBounds ctx.raw)
    (neighbors : WorklistNeighbors ctx root P) (owner : ValueOwnerSatisfies P v) :
    WorklistNeighbors (WfRewriter.replaceValue ctx _ v different oldIn newIn) root P := by
  constructor
  · intro w mem
    rw [OperationPtr.getOperands!_WfRewriter_replaceValue (by grind [ValuePtr.InBounds, OpResultPtr.InBounds])] at mem
    obtain ⟨x, hx, eq⟩ := Array.mem_map.mp mem
    split at eq <;> subst w
    · exact owner
    · exact neighbors.defs _ hx
  · intro op hin j mem
    have inside : op.InBounds ctx.raw := by grind
    rw [OperationPtr.getOperands!_WfRewriter_replaceValue inside] at mem
    obtain ⟨x, hx, eq⟩ := Array.mem_map.mp mem
    split at eq
    · rename_i equal
      exact neighbors.users op inside i (equal ▸ hx)
    · exact neighbors.users op inside j (eq ▸ hx)

private theorem InsertBeforeChain.worklist {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpCode} (chain : InsertBeforeChain root ops before after)
    (rw : PatternRewriter OpCode) (same : rw.ctx = before) (all : rw.worklist.All P)
    (fresh : ∀ op ∈ ops, P op) :
    let final := ops.foldl (fun (r : PatternRewriter OpCode) op => r.insertOp! op (.before root)) rw
    final.ctx = after ∧ final.worklist.All P := by
  induction chain generalizing rw with
  | nil => exact ⟨same, all⟩
  | cons op inside rootIn inserted tail ih =>
    apply ih (rw.insertOp! op (.before root))
    · rw [PatternRewriter.insertOpBang_ctx, same, insertOpBang_eq_of_insertOp inserted]
    · exact all.push (fresh _ (by simp))
    · exact fun op mem => fresh op (by simp [mem])

private theorem ReplaceResultChain.worklist {root : OperationPtr} {pairs : List (ValuePtr × Nat)}
    {before after : WfIRContext OpCode} (chain : ReplaceResultChain root pairs before after)
    (rw : PatternRewriter OpCode) (same : rw.ctx = before) (all : rw.worklist.All P)
    (neighbors : WorklistNeighbors before root P)
    (owners : ∀ p ∈ pairs, ValueOwnerSatisfies P p.1) :
    let final := pairs.foldl (fun (r : PatternRewriter OpCode) p => r.replaceValue! (root.getResult p.2) p.1) rw
    final.ctx = after ∧ final.worklist.All P ∧ WorklistNeighbors after root P := by
  induction chain generalizing rw with
  | nil => exact ⟨same, all, neighbors⟩
  | cons v i different oldIn newIn tail ih =>
    apply ih (rw.replaceValue! (root.getResult i) v)
    · rw [PatternRewriter.replaceValueBang_ctx, same, replaceValueBang_eq different oldIn newIn]
    · apply PatternRewriter.all_replaceValue! _ _ _ (by simpa only [same] using oldIn) all
      intro op bound mem
      rw [same] at bound mem
      exact neighbors.users op bound i mem
    · exact neighbors.replace different oldIn newIn (owners (v, i) (by simp))
    · exact fun p mem => owners p (by simp [mem])

/-- During a splice all old worklist entries, the inserted operations, and both sets of
SSA neighbors stay within any predicate closed under the verified edges. -/
theorem Pattern.fromLocalRewrite_worklist (rule : Pattern OpCode)
    {rw result : PatternRewriter OpCode} {op : OperationPtr} {opIn : op.InBounds rw.ctx.raw}
    {created : WfIRContext OpCode} {ops : Array OperationPtr} {values : Array ValuePtr}
    (localRun : rule.interpret rw.ctx op = some (created, some (ops, values)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rw op opIn = some result)
    (attached : (op.getParent! rw.ctx.raw).isSome) (regionless : op.getNumRegions! rw.ctx.raw = 0)
    (all : rw.worklist.All P) (ok : P op)
    (closed : ∀ p, p.InBounds rw.ctx.raw → P p → ∀ v ∈ p.getOperands! rw.ctx.raw, ValueOwnerSatisfies P v)
    (users : ∀ p, p.InBounds rw.ctx.raw → ∀ i, (op.getResult i : ValuePtr) ∈ p.getOperands! rw.ctx.raw → P p)
    (unallocated : ∀ p, ¬p.InBounds rw.ctx.raw → P p) :
    result.worklist.All P := by
  have notOwn := fromLocalRewrite_result_notOwn_indexed localRun run
  obtain ⟨inserted, replaced, insertions, substitutions, rootIn, regions, unused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regionless notOwn
  obtain ⟨fresh, _, _⟩ := rule.interpret_structure localRun
  have freshOk : ∀ p ∈ ops, P p := fun p mem => unallocated p ((fresh p).mp mem).2
  have replacementOk := rule.replacementOwners closed ok opIn localRun freshOk
  let start := {rw with ctx := created, hasDoneAction := true}
  obtain ⟨ictx, iw⟩ := insertions.worklist start rfl all (by simpa using freshOk)
  have operands (p : OperationPtr) (bound : p.InBounds rw.ctx.raw) :
      p.getOperands! inserted.raw = p.getOperands! rw.ctx.raw := by
    rw [insertions.preserves_operands]
    exact (rule.interpret_preserves_existing_fields localRun p bound).2
  have neighbors : WorklistNeighbors inserted op P := by
    constructor
    · rw [operands op opIn]
      exact closed op opIn ok
    · intro p _ i member
      by_cases bound : p.InBounds rw.ctx.raw
      · exact users p bound i (by simpa only [operands p bound] using member)
      · exact unallocated p bound
  obtain ⟨rctx, rwAll, edges⟩ := substitutions.worklist _ ictx iw neighbors (by
    intro pair mem
    exact replacementOk _ (by
      have hm : pair ∈ values.toList.zipIdx := by simpa using mem
      simpa using List.fst_mem_of_mem_zipIdx hm))
  rw [fromLocalRewrite_eq_folds localRun run]
  simp only [← Array.foldl_toList]
  have finish (r : PatternRewriter OpCode) (eq : r.ctx = replaced) (h : r.worklist.All P) :
      (r.eraseOp! op).worklist.All P := by
    unfold PatternRewriter.eraseOp!
    split <;> try contradiction
    · split
      · split
        · apply PatternRewriter.all_eraseOp _ _ _ _ _ h
          simpa only [eq, ValueOwnerSatisfies] using edges.defs
        · grind
      · grind
    · grind
  exact finish _ rctx rwAll

end Veir.Puddle
