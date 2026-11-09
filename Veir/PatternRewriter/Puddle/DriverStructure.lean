module

public import Veir.PatternRewriter.Puddle.CreationStructure
public import Veir.PatternRewriter.Puddle.ReplacementScope
public import Veir.Interpreter.Refinement.Basic
public import Veir.Rewriter.WfRewriter.GetSet
public import Veir.Rewriter.WfRewriter.InBounds
import all Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.CreationStructure
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.Rewriter.InsertPoint
import all Veir.IR.Basic

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Operation metadata and ownership untouched by local SSA-use replacement. -/
structure OperationHeaderPreserved (before after : IRContext OpInfo) (op : OperationPtr) : Prop where
  opcode : op.getOpType! after = op.getOpType! before
  properties : ∀ {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect] (code : Dialect),
    op.getProperties! after code = op.getProperties! before code
  resultTypes : op.getResultTypes! after = op.getResultTypes! before
  successors : op.getSuccessors! after = op.getSuccessors! before
  numRegions : op.getNumRegions! after = op.getNumRegions! before
  region : ∀ index, op.getRegion! after index = op.getRegion! before index
  parent : op.getParent! after = op.getParent! before
  parentOp : op.getParentOp! after = op.getParentOp! before

theorem OperationHeaderPreserved.refl (ctx : IRContext OpInfo) (op : OperationPtr) :
    OperationHeaderPreserved ctx ctx op := by constructor <;> intros <;> rfl

theorem OperationHeaderPreserved.trans {a b c : IRContext OpInfo} {op : OperationPtr}
    (hab : OperationHeaderPreserved a b op) (hbc : OperationHeaderPreserved b c op) :
    OperationHeaderPreserved a c op := by
  exact ⟨hbc.opcode.trans hab.opcode, fun code => (hbc.properties code).trans (hab.properties code),
    hbc.resultTypes.trans hab.resultTypes, hbc.successors.trans hab.successors,
    hbc.numRegions.trans hab.numRegions, fun i => (hbc.region i).trans (hab.region i),
    hbc.parent.trans hab.parent, hbc.parentOp.trans hab.parentOp⟩

/-- Inserting a new operation preserves every other operation's semantic header. -/
theorem operationHeaderPreserved_of_insertOp {before after : WfIRContext OpInfo}
    {newOp op : OperationPtr} {ip : InsertPoint}
    {newIn : newOp.InBounds before.raw} {ipIn : ip.InBounds before.raw}
    (inserted : WfRewriter.insertOp before newOp ip newIn ipIn = some after) (different : op ≠ newOp) :
    OperationHeaderPreserved before.raw after.raw op := by
  constructor <;> intros <;> grind [OperationPtr.getParentOp!, OperationPtr.getParentRegion!]

/-- Replacing SSA uses leaves opcode, metadata, regions, successors, and ownership intact. -/
theorem operationHeaderPreserved_of_replaceValue {before : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} {different : oldValue ≠ newValue}
    {oldIn : oldValue.InBounds before.raw} {newIn : newValue.InBounds before.raw} (op : OperationPtr) :
    OperationHeaderPreserved before.raw
      (WfRewriter.replaceValue before oldValue newValue different oldIn newIn).raw op := by
  constructor <;> intros <;> simp [OperationPtr.getParentOp!, OperationPtr.getParentRegion!]

/-- Successful checked insertion is exactly the bang insertion used by the driver. -/
theorem insertOpBang_eq_of_insertOp {before after : WfIRContext OpInfo}
    {newOp : OperationPtr} {ip : InsertPoint}
    {newIn : newOp.InBounds before.raw} {ipIn : ip.InBounds before.raw}
    (inserted : WfRewriter.insertOp before newOp ip newIn ipIn = some after) :
    WfRewriter.insertOp! before newOp ip = after := by
  simp [WfRewriter.insertOp!, newIn, ipIn, inserted]

/-- Safe value replacement exposes the exact operand renaming performed by the driver. -/
theorem operands_replaceValueBang {before : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} (different : oldValue ≠ newValue)
    (oldIn : oldValue.InBounds before.raw) (newIn : newValue.InBounds before.raw)
    (op : OperationPtr) (opIn : op.InBounds before.raw) :
    op.getOperands! (WfRewriter.replaceValue! before oldValue newValue).raw =
      (op.getOperands! before.raw).map (fun value => if value = oldValue then newValue else value) := by
  unfold WfRewriter.replaceValue!
  split
  · exact OperationPtr.getOperands!_WfRewriter_replaceValue opIn
  · contradiction

theorem replaceValueBang_eq {before : WfIRContext OpInfo} {oldValue newValue : ValuePtr}
    (different : oldValue ≠ newValue) (oldIn : oldValue.InBounds before.raw)
    (newIn : newValue.InBounds before.raw) :
    WfRewriter.replaceValue! before oldValue newValue =
      WfRewriter.replaceValue before oldValue newValue different oldIn newIn := by
  unfold WfRewriter.replaceValue!
  split
  · rfl
  · contradiction

/-- The root's predecessor becomes the operation inserted immediately before it. -/
theorem root_prev_of_insertBefore {before after : WfIRContext OpInfo} {root newOp : OperationPtr}
    {newIn : newOp.InBounds before.raw} {rootIn : root.InBounds before.raw}
    (inserted : WfRewriter.insertOp before newOp (.before root) newIn (by simpa using rootIn) = some after) :
    root.getPrevOp! after.raw = some newOp := by
  have h := OperationPtr.getPrevOp!_wfRewriter_insertOp (operation := root) inserted
  simpa [InsertPoint.next] using h

/-- An inserted operation links forward to the old root and back to the old predecessor. -/
theorem newOp_links_of_insertBefore {before after : WfIRContext OpInfo} {root newOp : OperationPtr}
    {newIn : newOp.InBounds before.raw} {rootIn : root.InBounds before.raw}
    (inserted : WfRewriter.insertOp before newOp (.before root) newIn (by simpa using rootIn) = some after)
    (different : newOp ≠ root) (notPredecessor : root.getPrevOp! before.raw ≠ some newOp) :
    newOp.getPrevOp! after.raw = root.getPrevOp! before.raw ∧ newOp.getNextOp! after.raw = some root := by
  constructor
  · have h := OperationPtr.getPrevOp!_wfRewriter_insertOp (operation := newOp) inserted
    simpa [InsertPoint.next, InsertPoint.prev!, different] using h
  · have h := OperationPtr.getNextOp!_wfRewriter_insertOp (operation := newOp) inserted
    simpa [InsertPoint.next, InsertPoint.prev!, Ne.symm notPredecessor] using h

theorem operationHeaderPreserved_of_eraseOp {before : WfIRContext OpInfo}
    {root op : OperationPtr} {regions : root.getNumRegions! before.raw = 0}
    {unused : !root.hasUses! before.raw} {rootIn : root.InBounds before.raw}
    (different : op ≠ root) (opIn : op.InBounds before.raw) :
    OperationHeaderPreserved before.raw (WfRewriter.eraseOp before root regions unused rootIn).raw op := by
  have hafter : op.InBounds (WfRewriter.eraseOp before root regions unused rootIn).raw := by
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (GenericPtr.operation op) different).mpr opIn
  constructor <;> intros <;> grind [OperationPtr.getParentOp!, OperationPtr.getParentRegion!]

/-- Removing a dead root reconnects its surviving predecessor to the old successor. -/
theorem predecessor_next_of_eraseOp {before : WfIRContext OpInfo} {root predecessor : OperationPtr}
    {regions : root.getNumRegions! before.raw = 0} {unused : !root.hasUses! before.raw}
    {rootIn : root.InBounds before.raw}
    (previous : root.getPrevOp! before.raw = some predecessor) (different : predecessor ≠ root)
    (predecessorIn : predecessor.InBounds before.raw) :
    predecessor.getNextOp! (WfRewriter.eraseOp before root regions unused rootIn).raw =
      root.getNextOp! before.raw := by
  have hafter : predecessor.InBounds (WfRewriter.eraseOp before root regions unused rootIn).raw := by
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (GenericPtr.operation predecessor) different).mpr predecessorIn
  simpa [previous] using OperationPtr.getNextOp!_wfRewriter_eraseOp hafter

theorem PatternRewriter.insertOpBang_ctx (rewriter : PatternRewriter OpInfo)
    (op : OperationPtr) (ip : InsertPoint) :
    (rewriter.insertOp! op ip).ctx = WfRewriter.insertOp! rewriter.ctx op ip := by
  simp [Veir.PatternRewriter.insertOp!]

theorem PatternRewriter.replaceValueBang_ctx (rewriter : PatternRewriter OpInfo)
    (oldValue newValue : ValuePtr) :
    (rewriter.replaceValue! oldValue newValue).ctx = WfRewriter.replaceValue! rewriter.ctx oldValue newValue := by
  simp [Veir.PatternRewriter.replaceValue!, WfRewriter.replaceValue!,
    Veir.PatternRewriter.addUsersInWorklist_same_ctx]
  repeat first | split | rfl

theorem PatternRewriter.eraseOpBang_ctx (rewriter : PatternRewriter OpInfo) (op : OperationPtr) :
    (rewriter.eraseOp! op).ctx = WfRewriter.eraseOp! rewriter.ctx op := by
  simp [Veir.PatternRewriter.eraseOp!, WfRewriter.eraseOp!, Veir.PatternRewriter.eraseOp]
  repeat first | split | rfl


/-- The concrete context transformation performed after a local pattern returns replacement data. -/
@[expose]
def driverContext (created : WfIRContext OpInfo) (root : OperationPtr)
    (newOps : Array OperationPtr) (replacements : Array ValuePtr) : WfIRContext OpInfo :=
  let inserted := newOps.foldl (fun ctx op => WfRewriter.insertOp! ctx op (.before root)) created
  let replaced := replacements.zipIdx.foldl
    (fun ctx pair => WfRewriter.replaceValue! ctx (root.getResult pair.2) pair.1) inserted
  WfRewriter.eraseOp! replaced root

/-- A successful driver run establishes replacement arity before any context mutation. -/
theorem fromLocalRewrite_result_arity {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result) :
    replacements.size = root.getNumResults! created.raw := by
  simp only [RewritePattern.fromLocalRewrite, localRun, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at run
  obtain ⟨u, hguard, _⟩ := run
  simpa [guard] using hguard

/-- Successful local execution rejects every replacement aliasing an original root result,
including aliases hidden behind distinct matcher handles. -/
theorem fromLocalRewrite_result_notOwn {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result) :
    ∀ value ∈ replacements, value ∉ root.getResults! rewriter.ctx.raw := by
  simp only [RewritePattern.fromLocalRewrite, localRun, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at run
  obtain ⟨_, _, _, checked, _⟩ := run
  simpa [guard] using checked

/-- Successful runtime alias checks supply the safe driver's indexed exclusion contract. -/
theorem fromLocalRewrite_result_notOwn_indexed {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result) :
    ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value := by
  intro value member index bound same
  have checked := fromLocalRewrite_result_notOwn localRun run value member
  apply checked
  rw [← same]
  exact OperationPtr.getResults!.mem_getResult bound

/-- A successful local driver execution consists of exactly its two ordered folds and erasure. -/
theorem fromLocalRewrite_eq_folds {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result) :
    result = ((replacements.zipIdx.foldl
      (fun (r : PatternRewriter OpInfo) pair => r.replaceValue! (root.getResult pair.2) pair.1)
      (newOps.foldl (fun (r : PatternRewriter OpInfo) op => r.insertOp! op (.before root))
        { rewriter with ctx := created, hasDoneAction := true })).eraseOp! root) := by
  have harity := fromLocalRewrite_result_arity localRun run
  have hnotOwn := fromLocalRewrite_result_notOwn localRun run
  simp only [RewritePattern.fromLocalRewrite, localRun] at run
  simp only [guard, harity, ite_eq_left hnotOwn, ↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at run
  have hinsertFold := Array.forIn_pure_yield_eq_foldl (m := Option) (xs := newOps)
    (fun (op : OperationPtr) (r : PatternRewriter OpInfo) => r.insertOp! op (.before root))
    { rewriter with ctx := created, hasDoneAction := true }
  simp only [Option.pure_def] at hinsertFold
  rw [hinsertFold] at run
  simp only [Option.bind_some] at run
  have hfold := Array.forIn_pure_yield_eq_foldl (m := Option) (xs := replacements.zipIdx)
    (fun (pair : ValuePtr × Nat) (r : PatternRewriter OpInfo) =>
      r.replaceValue! (root.getResult pair.2) pair.1)
    (newOps.foldl (fun r op => r.insertOp! op (.before root))
      { rewriter with ctx := created, hasDoneAction := true })
  simp only [Option.pure_def] at hfold
  rw [hfold] at run
  simpa only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.some.injEq] using run.symm

/-- Worklist maintenance does not alter the context transformation of a successful local rewrite. -/
theorem fromLocalRewrite_ctx {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result) :
    result.ctx = driverContext created root newOps replacements := by
  rw [fromLocalRewrite_eq_folds localRun run, PatternRewriter.eraseOpBang_ctx]
  unfold driverContext
  congr 1
  rw [← Array.foldl_hom (g₂ := fun (ctx : WfIRContext OpInfo) (pair : ValuePtr × Nat) =>
      WfRewriter.replaceValue! ctx (root.getResult pair.2) pair.1)
    (fun r : PatternRewriter OpInfo => r.ctx)
    (fun r pair => (PatternRewriter.replaceValueBang_ctx r (root.getResult pair.2) pair.1).symm)]
  rw [← Array.foldl_hom (g₂ := fun (ctx : WfIRContext OpInfo) (op : OperationPtr) =>
      WfRewriter.insertOp! ctx op (.before root))
    (fun r : PatternRewriter OpInfo => r.ctx)
    (fun r op => (PatternRewriter.insertOpBang_ctx r op (.before root)).symm)]


/-- Checked insertions, in the same order as the driver's insertion fold. -/
inductive InsertBeforeChain (root : OperationPtr) :
    List OperationPtr → WfIRContext OpInfo → WfIRContext OpInfo → Prop
  | nil (ctx) : InsertBeforeChain root [] ctx ctx
  | cons {before middle after rest} (op)
      (opIn : op.InBounds before.raw) (rootIn : root.InBounds before.raw)
      (inserted : WfRewriter.insertOp before op (.before root) opIn (by simpa using rootIn) = some middle)
      (tail : InsertBeforeChain root rest middle after) :
      InsertBeforeChain root (op :: rest) before after

theorem InsertBeforeChain.eq_fold {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after) :
    ops.foldl (fun ctx op => WfRewriter.insertOp! ctx op (.before root)) before = after := by
  induction chain with
  | nil => rfl
  | cons op opIn rootIn inserted tail ih =>
    simpa [List.foldl_cons, insertOpBang_eq_of_insertOp inserted] using ih

theorem InsertBeforeChain.inBounds {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (op : OperationPtr) (opIn : op.InBounds before.raw) : op.InBounds after.raw := by
  induction chain with
  | nil => exact opIn
  | cons insertedOp newIn rootIn inserted tail ih => exact ih (by grind)

theorem InsertBeforeChain.genericInBounds {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (ptr : GenericPtr) (ptrIn : ptr.InBounds before.raw) : ptr.InBounds after.raw := by
  induction chain with
  | nil => exact ptrIn
  | cons insertedOp newIn rootIn inserted tail ih => exact ih (by grind)

theorem InsertBeforeChain.preserves_header {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (op : OperationPtr) (notInserted : op ∉ ops) : OperationHeaderPreserved before.raw after.raw op := by
  induction chain with
  | nil => exact .refl _ _
  | cons newOp newIn rootIn inserted tail ih =>
    have hne : op ≠ newOp := by intro h; subst op; simp at notInserted
    exact (operationHeaderPreserved_of_insertOp inserted hne).trans
      (ih (fun hm => notInserted (List.mem_cons_of_mem _ hm)))

theorem InsertBeforeChain.preserves_operands {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (op : OperationPtr) : op.getOperands! after.raw = op.getOperands! before.raw := by
  induction chain with
  | nil => rfl
  | cons newOp newIn rootIn inserted tail ih =>
    rw [ih]
    exact OperationPtr.getOperands!_wfRewriter_insertOp inserted

/-- Checked result-use substitutions in driver order, before erasing the old root. -/
inductive ReplaceResultChain (root : OperationPtr) :
    List (ValuePtr × Nat) → WfIRContext OpInfo → WfIRContext OpInfo → Prop
  | nil (ctx) : ReplaceResultChain root [] ctx ctx
  | cons {before after rest} (value : ValuePtr) (index : Nat)
      (different : root.getResult index ≠ value)
      (oldIn : (root.getResult index : ValuePtr).InBounds before.raw) (newIn : value.InBounds before.raw)
      (tail : ReplaceResultChain root rest
        (WfRewriter.replaceValue before (root.getResult index) value different oldIn newIn) after) :
      ReplaceResultChain root ((value, index) :: rest) before after

@[expose]
def renameRootResults (root : OperationPtr) (replacements : List (ValuePtr × Nat)) (value : ValuePtr) : ValuePtr :=
  match replacements with
  | [] => value
  | (replacement, index) :: rest =>
      renameRootResults root rest (if value = root.getResult index then replacement else value)

theorem ReplaceResultChain.eq_fold {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after) :
    replacements.foldl (fun ctx pair => WfRewriter.replaceValue! ctx (root.getResult pair.2) pair.1) before = after := by
  induction chain with
  | nil => rfl
  | cons value index different oldIn newIn tail ih =>
    simpa only [List.foldl_cons, replaceValueBang_eq different oldIn newIn] using ih

theorem ReplaceResultChain.inBounds {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (op : OperationPtr) (opIn : op.InBounds before.raw) : op.InBounds after.raw := by
  induction chain with
  | nil => exact opIn
  | cons value index different oldIn newIn tail ih => exact ih (by grind)

theorem ReplaceResultChain.preserves_header {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (op : OperationPtr) : OperationHeaderPreserved before.raw after.raw op := by
  induction chain with
  | nil => exact .refl _ _
  | cons value index different oldIn newIn tail ih =>
    exact (operationHeaderPreserved_of_replaceValue op).trans ih

theorem ReplaceResultChain.operands {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (op : OperationPtr) (opIn : op.InBounds before.raw) :
    op.getOperands! after.raw = (op.getOperands! before.raw).map (renameRootResults root replacements) := by
  induction chain with
  | nil => simp [renameRootResults]
  | cons value index different oldIn newIn tail ih =>
    rw [ih (by grind), OperationPtr.getOperands!_WfRewriter_replaceValue opIn]
    simp only [Array.map_map, Function.comp_def, renameRootResults]


theorem eraseOpBang_eq {before : WfIRContext OpInfo} {root : OperationPtr}
    (rootIn : root.InBounds before.raw) (regions : root.getNumRegions! before.raw = 0)
    (unused : !root.hasUses! before.raw) :
    WfRewriter.eraseOp! before root = WfRewriter.eraseOp before root regions unused rootIn := by
  simp [WfRewriter.eraseOp!, rootIn, regions, unused]

theorem driverContext_eq_of_chains {created inserted replaced : WfIRContext OpInfo}
    {root : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootIn : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) :
    driverContext created root newOps replacements = WfRewriter.eraseOp replaced root regions unused rootIn := by
  have hi := insertions.eq_fold
  have hr := substitutions.eq_fold
  rw [Array.foldl_toList] at hi hr
  simp only [driverContext, hi, hr, eraseOpBang_eq rootIn regions unused]

/-- The actual driver preserves surviving operation headers and remaps exactly their operands.
Checked phase chains rule out the bang APIs' panic defaults. -/
theorem fromLocalRewrite_operation_frame {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created inserted replaced : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result)
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootInReplaced : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw)
    (op : OperationPtr) (opIn : op.InBounds created.raw) (different : op ≠ root)
    (notInserted : op ∉ newOps.toList) :
    OperationHeaderPreserved created.raw result.ctx.raw op ∧
      op.getOperands! result.ctx.raw =
        (op.getOperands! created.raw).map (renameRootResults root replacements.zipIdx.toList) := by
  have hctx := fromLocalRewrite_ctx localRun run
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced regions unused] at hctx
  rw [hctx]
  have hopInserted := insertions.inBounds op opIn
  have hopReplaced := substitutions.inBounds op hopInserted
  have hopErased : op.InBounds (WfRewriter.eraseOp replaced root regions unused rootInReplaced).raw := by
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (GenericPtr.operation op) different).mpr hopReplaced
  constructor
  · exact ((insertions.preserves_header op notInserted).trans (substitutions.preserves_header op)).trans
      (operationHeaderPreserved_of_eraseOp different hopReplaced)
  · rw [OperationPtr.getOperands!_wfRewriter_eraseOp hopErased,
      substitutions.operands op hopInserted, insertions.preserves_operands op]


/-- Preserving an operation's header retains its function name and module membership. -/
theorem OperationHeaderPreserved.isTopLevelFuncWithName {before after : IRContext OpCode}
    {op moduleOp : OperationPtr} {name : StringAttr}
    (header : OperationHeaderPreserved before after op)
    (source : op.IsTopLevelFuncWithName moduleOp before name) :
    op.IsTopLevelFuncWithName moduleOp after name := by
  refine ⟨header.opcode.trans source.isFunc, ?_, header.parentOp.trans source.isTopLevel⟩
  have hp := header.properties Func.func
  exact source.hasName.trans (congrArg (fun props : FuncFuncProperties => props.sym_name) hp).symm

/-- Actual Puddle creation never alters the semantic header of an existing operation. -/
theorem CreateDecl.preserves_existing_header_of_run (decl : CreateDecl OpCode)
    {before after : WfIRContext OpCode} {assignment final : Assignment OpCode}
    {newOps : Array OperationPtr} (run : decl.run assignment before = some (after, newOps, final))
    (op : OperationPtr) (opIn : op.InBounds before.raw) :
    OperationHeaderPreserved before.raw after.raw op := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, _, _⟩ := run
    exact .refl _ _
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨bound, _, rfl, _, _⟩ := run
    exact .refl _ _
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨values, _, outputValues, _, bound, _, rfl, _, _⟩ := run
    exact .refl _ _
  | operation code operands types properties opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨operandPtrs, _, resultTypes, _, property, _, u, _, hrun⟩ := run
    split at hrun
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨⟨created, newOp⟩, hcreate, bound, _, boundResults, _, rfl, _, _⟩ := hrun
      constructor <;> intros <;> grind [OperationPtr.getParentOp!, OperationPtr.getParentRegion!]
    · contradiction

theorem CreateProg.preserves_existing_header_of_runDecls (decls : List (CreateDecl OpCode))
    {before after : WfIRContext OpCode} {assignment final : Assignment OpCode}
    {newOps : Array OperationPtr}
    (run : CreateProg.runDecls decls before assignment = some (after, newOps, final))
    (op : OperationPtr) (opIn : op.InBounds before.raw) :
    OperationHeaderPreserved before.raw after.raw op := by
  induction decls generalizing before assignment newOps final with
  | nil =>
    simp only [CreateProg.runDecls, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, _, _⟩ := run
    exact .refl _ _
  | cons decl rest ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨middle, firstOps, middleAssignment⟩, hfirst, ⟨last, restOps, finalAssignment⟩,
      hrest, rfl, _, _⟩ := run
    have hopMiddle := (CreateDecl.run_withCreatedOps decl _ _ _ _ _ hfirst).inBounds_mono
      (GenericPtr.operation op) opIn
    exact (CreateDecl.preserves_existing_header_of_run decl hfirst op opIn).trans
      (ih hrest hopMiddle)


theorem exists_insertBefore {before : WfIRContext OpInfo} {root newOp : OperationPtr}
    (rootIn : root.InBounds before.raw) (newIn : newOp.InBounds before.raw)
    (attached : (root.getParent! before.raw).isSome = true)
    (detached : newOp.getParent! before.raw = none) :
    ∃ after, WfRewriter.insertOp before newOp (.before root) newIn (by simpa using rootIn) = some after := by
  cases h : WfRewriter.insertOp before newOp (.before root) newIn (by simpa using rootIn) with
  | some after => exact ⟨after, rfl⟩
  | none =>
    simp only [WfRewriter.insertOp] at h
    grind (gen := 20) [Rewriter.insertOp, InsertPoint.block, InsertPoint.next, OperationPtr.linkBetweenWithParent,
      OperationPtr.setParentWithCheck]

/-- The driver insertion phase has a checked execution when all returned operations are in bounds
and distinct from the attached root. -/
theorem exists_insertBeforeChain (ops : List OperationPtr) {before : WfIRContext OpInfo}
    {root : OperationPtr} (rootIn : root.InBounds before.raw)
    (attached : (root.getParent! before.raw).isSome = true)
    (allIn : ∀ op ∈ ops, op.InBounds before.raw) (notRoot : root ∉ ops)
    (detached : ∀ op ∈ ops, op.getParent! before.raw = none) (nodup : ops.Nodup) :
    ∃ after, InsertBeforeChain root ops before after := by
  induction ops generalizing before with
  | nil => exact ⟨before, .nil _⟩
  | cons op rest ih =>
    have opIn := allIn op (by simp)
    obtain ⟨middle, hinsert⟩ := exists_insertBefore rootIn opIn attached (detached op (by simp))
    have hne : root ≠ op := by intro h; subst op; simp at notRoot
    have hrootMiddle : root.InBounds middle.raw := by grind
    have hrootParent : root.getParent! middle.raw = root.getParent! before.raw :=
      (operationHeaderPreserved_of_insertOp hinsert hne).parent
    obtain ⟨after, htail⟩ := ih hrootMiddle (by simpa [hrootParent] using attached)
      (fun other hm => by have := allIn other (List.mem_cons_of_mem _ hm); grind)
      (fun hm => notRoot (List.mem_cons_of_mem _ hm))
      (fun other hm => by
        have hne : other ≠ op := by
          intro heq; subst other; exact (List.nodup_cons.mp nodup).1 hm
        rw [(operationHeaderPreserved_of_insertOp hinsert hne).parent]
        exact detached other (List.mem_cons_of_mem _ hm))
      (List.nodup_cons.mp nodup).2
    exact ⟨after, .cons op opIn rootIn hinsert htail⟩


theorem WfRewriter.replaceValue_old_unused {before : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} {different : oldValue ≠ newValue}
    {oldIn : oldValue.InBounds before.raw} {newIn : newValue.InBounds before.raw} :
    oldValue.hasUses! (WfRewriter.replaceValue before oldValue newValue different oldIn newIn).raw = false := by
  fun_induction WfRewriter.replaceValue <;> grind [Id.run, ValuePtr.hasUses!_def]


theorem replaceUse_preserves_unused {before : WfIRContext OpInfo}
    {use : OpOperandPtr} {newValue value : ValuePtr}
    {useIn : use.InBounds before.raw} {newIn : newValue.InBounds before.raw}
    (_valueIn : value.InBounds before.raw) (notNew : value ≠ newValue)
    (unused : value.hasUses! before.raw = false) :
    value.hasUses! (Rewriter.replaceUse before.raw use newValue useIn newIn (by grind)) = false := by
  unfold Rewriter.replaceUse
  split
  · exact unused
  · simp only [ValuePtr.hasUses!_def] at unused ⊢
    grind (gen := 15)

theorem WfRewriter.replaceValue_preserves_unused {before : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} {different : oldValue ≠ newValue}
    {oldIn : oldValue.InBounds before.raw} {newIn : newValue.InBounds before.raw}
    (value : ValuePtr) (valueIn : value.InBounds before.raw)
    (notNew : value ≠ newValue) (unused : value.hasUses! before.raw = false) :
    value.hasUses! (WfRewriter.replaceValue before oldValue newValue different oldIn newIn).raw = false := by
  fun_induction WfRewriter.replaceValue <;>
    grind [Id.run, replaceUse_preserves_unused]


theorem ReplaceResultChain.preserves_unused {root : OperationPtr}
    {replacements : List (ValuePtr × Nat)} {before after : WfIRContext OpInfo}
    (chain : ReplaceResultChain root replacements before after) (value : ValuePtr)
    (valueIn : value.InBounds before.raw) (notReplacement : ∀ pair ∈ replacements, value ≠ pair.1)
    (unused : value.hasUses! before.raw = false) : value.hasUses! after.raw = false := by
  induction chain with
  | nil => exact unused
  | cons replacement index different oldIn newIn tail ih =>
    apply ih (by grind) (fun pair hm => notReplacement pair (List.mem_cons_of_mem _ hm))
    exact WfRewriter.replaceValue_preserves_unused value valueIn
      (notReplacement (replacement, index) (by simp)) unused

theorem ReplaceResultChain.replaced_unused {root : OperationPtr}
    {replacements : List (ValuePtr × Nat)} {before after : WfIRContext OpInfo}
    (chain : ReplaceResultChain root replacements before after) (index : Nat)
    (valueIn : (root.getResult index : ValuePtr).InBounds before.raw)
    (covered : index ∈ replacements.map Prod.snd)
    (notReplacement : ∀ pair ∈ replacements, (root.getResult index : ValuePtr) ≠ pair.1) :
    (root.getResult index : ValuePtr).hasUses! after.raw = false := by
  induction chain with
  | nil => simp at covered
  | cons replacement i different oldIn newIn tail ih =>
    rcases List.mem_cons.mp covered with heq | htail
    · subst index
      apply tail.preserves_unused _ (by grind)
        (fun pair hm => notReplacement pair (List.mem_cons_of_mem _ hm))
      exact WfRewriter.replaceValue_old_unused
    · exact ih (by grind) htail (fun pair hm => notReplacement pair (List.mem_cons_of_mem _ hm))

/-- Covering every old result and never replacing with an old result makes root erasure safe. -/
theorem ReplaceResultChain.root_unused {root : OperationPtr}
    {replacements : List (ValuePtr × Nat)} {before after : WfIRContext OpInfo}
    (chain : ReplaceResultChain root replacements before after) (rootIn : root.InBounds before.raw)
    (covered : ∀ index < root.getNumResults! before.raw, index ∈ replacements.map Prod.snd)
    (notReplacement : ∀ index < root.getNumResults! before.raw,
      ∀ pair ∈ replacements, (root.getResult index : ValuePtr) ≠ pair.1) :
    root.hasUses! after.raw = false := by
  have hs : root.getNumResults! after.raw = root.getNumResults! before.raw := by
    have htypes := (chain.preserves_header root).resultTypes
    have hsize := congrArg Array.size htypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using hsize
  apply OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false.mpr
  intro index hi
  have hindex : index < root.getNumResults! before.raw := by simpa [hs] using hi
  exact chain.replaced_unused index (by grind) (covered index hindex) (notReplacement index hindex)


theorem exists_replaceResultChain (replacements : List (ValuePtr × Nat))
    {before : WfIRContext OpInfo} {root : OperationPtr}
    (allIn : ∀ pair ∈ replacements,
      (root.getResult pair.2 : ValuePtr).InBounds before.raw ∧ pair.1.InBounds before.raw)
    (different : ∀ pair ∈ replacements, (root.getResult pair.2 : ValuePtr) ≠ pair.1) :
    ∃ after, ReplaceResultChain root replacements before after := by
  induction replacements generalizing before with
  | nil => exact ⟨before, .nil _⟩
  | cons pair rest ih =>
    rcases pair with ⟨value, index⟩
    have hbounds := allIn (value, index) (by simp)
    have hne := different (value, index) (by simp)
    obtain ⟨after, htail⟩ := ih
      (before := WfRewriter.replaceValue before (root.getResult index) value hne hbounds.1 hbounds.2)
      (fun other hm => by have := allIn other (List.mem_cons_of_mem _ hm); grind)
      (fun other hm => different other (List.mem_cons_of_mem _ hm))
    exact ⟨after, .cons value index hne hbounds.1 hbounds.2 htail⟩

/-- The driver's bang APIs follow checked paths when replacement data obeys the concrete contract. -/
theorem driver_safe_phases {created : WfIRContext OpInfo} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (rootIn : root.InBounds created.raw) (attached : (root.getParent! created.raw).isSome = true)
    (regions : root.getNumRegions! created.raw = 0)
    (opsIn : ∀ op ∈ newOps, op.InBounds created.raw)
    (detached : ∀ op ∈ newOps, op.getParent! created.raw = none) (nodup : newOps.toList.Nodup)
    (notRoot : root ∉ newOps)
    (valuesIn : ∀ value ∈ replacements, value.InBounds created.raw)
    (size : replacements.size = root.getNumResults! created.raw)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! created.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    ∃ inserted replaced, InsertBeforeChain root newOps.toList created inserted ∧
      ReplaceResultChain root replacements.zipIdx.toList inserted replaced ∧
      root.InBounds replaced.raw ∧ root.getNumRegions! replaced.raw = 0 ∧ !root.hasUses! replaced.raw := by
  obtain ⟨inserted, hinsert⟩ := exists_insertBeforeChain newOps.toList rootIn attached
    (by simpa using opsIn) (by simpa using notRoot) (by simpa using detached) nodup
  have hindex {pair : ValuePtr × Nat} (hm : pair ∈ replacements.zipIdx.toList) :
      pair.2 < root.getNumResults! created.raw ∧ pair.1 ∈ replacements := by
    have hm' : pair ∈ replacements.toList.zipIdx := by simpa using hm
    have hi := List.snd_lt_of_mem_zipIdx hm'
    have hv := List.fst_mem_of_mem_zipIdx hm'
    exact ⟨by simpa [← size] using hi, by simpa using hv⟩
  have hbounds : ∀ pair ∈ replacements.zipIdx.toList,
      (root.getResult pair.2 : ValuePtr).InBounds inserted.raw ∧ pair.1.InBounds inserted.raw := by
    intro pair hm
    have hi := hindex hm
    have hrootValue : (root.getResult pair.2 : ValuePtr).InBounds created.raw := by grind
    exact ⟨hinsert.genericInBounds (.value _) hrootValue,
      hinsert.genericInBounds (.value _) (valuesIn pair.1 hi.2)⟩
  obtain ⟨replaced, hreplace⟩ := exists_replaceResultChain replacements.zipIdx.toList hbounds
    (fun pair hm => notOwn pair.1 (hindex hm).2 pair.2 (hindex hm).1)
  have hrootInserted := hinsert.inBounds root rootIn
  have hs : root.getNumResults! inserted.raw = root.getNumResults! created.raw := by
    have ht := congrArg Array.size (hinsert.preserves_header root (by simpa using notRoot)).resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using ht
  have hcovered : ∀ index < root.getNumResults! inserted.raw,
      index ∈ replacements.zipIdx.toList.map Prod.snd := by
    intro index hi
    have hsize : index < replacements.size := by simpa [size, hs] using hi
    refine List.mem_map.mpr ⟨(replacements[index], index), ?_, rfl⟩
    simp only [Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?]
    simp [hsize]
  have hnoUses := hreplace.root_unused hrootInserted hcovered
    (fun index hi pair hm => notOwn pair.1 (hindex hm).2 index (by simpa [hs] using hi))
  have hregions : root.getNumRegions! replaced.raw = 0 := by
    rw [(hreplace.preserves_header root).numRegions,
      (hinsert.preserves_header root (by simpa using notRoot)).numRegions, regions]
  exact ⟨inserted, replaced, hinsert, hreplace, hreplace.inBounds root hrootInserted, hregions,
    by simp [hnoUses]⟩


theorem WfIRContext.WithCreatedOps.preserves_operands {before after : WfIRContext OpInfo}
    (created : WfIRContext.WithCreatedOps before after) (op : OperationPtr) (opIn : op.InBounds before.raw) :
    op.getOperands! after.raw = op.getOperands! before.raw := by
  induction created with
  | Nil => rfl
  | CreatedOp first middle last previous hcreate ih =>
    have hopMiddle := previous.inBounds_mono (.operation op) opIn
    obtain ⟨code, types, operands, successors, regions, properties, h₁, h₂, h₃, h₄, hcreate⟩ := hcreate
    have hopLast : op.getOperands! last.raw = op.getOperands! middle.raw := by grind
    exact hopLast.trans (ih opIn)

theorem Pattern.interpret_preserves_existing_fields (rule : Pattern OpCode)
    {before created : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (run : rule.interpret before root = some (created, some (newOps, replacements)))
    (op : OperationPtr) (opIn : op.InBounds before.raw) :
    OperationHeaderPreserved before.raw created.raw op ∧
      op.getOperands! created.raw = op.getOperands! before.raw := by
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ run
  refine ⟨?_, WfIRContext.WithCreatedOps.preserves_operands hcreated op opIn⟩
  unfold Pattern.interpret at run
  split at run
  · simp_all
  · split at run
    · contradiction
    · rename_i matched hmatch createdCtx createdOps finalAssignment hcreate
      split at run
      · contradiction
      · cases run
        exact CreateProg.preserves_existing_header_of_runDecls rule.creation.decls hcreate op opIn

theorem Pattern.fromLocalRewrite_safe_phases (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    ∃ inserted replaced, InsertBeforeChain root newOps.toList created inserted ∧
      ReplaceResultChain root replacements.zipIdx.toList inserted replaced ∧
      root.InBounds replaced.raw ∧ root.getNumRegions! replaced.raw = 0 ∧ !root.hasUses! replaced.raw := by
  obtain ⟨fresh, nodup, detached⟩ := rule.interpret_structure localRun
  have createdOps := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have rootInCreated := createdOps.inBounds_mono (.operation root) rootIn
  obtain ⟨rootHeader, _⟩ := rule.interpret_preserves_existing_fields localRun root rootIn
  have hnum : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    have ht := congrArg Array.size rootHeader.resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using ht
  exact driver_safe_phases rootInCreated (by simpa [rootHeader.parent] using attached)
    (rootHeader.numRegions.trans regions) (fun op hm => (fresh op).mp hm |>.1)
    (fun op hm => (detached op hm).1) nodup (fun hm => (fresh root).mp hm |>.2 <| rootIn)
    (rule.interpret_returnValuesInBounds_of_root rootIn localRun)
    (fromLocalRewrite_result_arity localRun run) (by simpa [hnum] using notOwn)

/-- A successful compiled local driver preserves every surviving old operation and its module
function identity, provided its concrete replacement array has the required arity and no old results. -/
theorem Pattern.fromLocalRewrite_existing_frame (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root) :
    OperationHeaderPreserved rewriter.ctx.raw result.ctx.raw op ∧
      op.getOperands! result.ctx.raw =
        (op.getOperands! rewriter.ctx.raw).map (renameRootResults root replacements.zipIdx.toList) := by
  obtain ⟨fresh, nodup, detached⟩ := rule.interpret_structure localRun
  have createdOps := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have rootInCreated := createdOps.inBounds_mono (.operation root) rootIn
  have opInCreated := createdOps.inBounds_mono (.operation op) opIn
  obtain ⟨rootHeader, _⟩ := rule.interpret_preserves_existing_fields localRun root rootIn
  have hnum : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    have ht := congrArg Array.size rootHeader.resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using ht
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ := driver_safe_phases
    rootInCreated (by simpa [rootHeader.parent] using attached) (rootHeader.numRegions.trans regions)
    (fun op hm => (fresh op).mp hm |>.1) (fun op hm => (detached op hm).1) nodup
    (fun hm => (fresh root).mp hm |>.2 <| rootIn)
    (rule.interpret_returnValuesInBounds_of_root rootIn localRun)
    (fromLocalRewrite_result_arity localRun run) (by simpa [hnum] using notOwn)
  have notInserted : op ∉ newOps.toList := by
    intro hm
    exact ((fresh op).mp (by simpa using hm)).2 opIn
  obtain ⟨driverHeader, hoperands⟩ := fromLocalRewrite_operation_frame localRun run hinsert hreplace
    hroot hregions hunused op opInCreated different notInserted
  obtain ⟨creationHeader, creationOperands⟩ := rule.interpret_preserves_existing_fields localRun op opIn
  exact ⟨creationHeader.trans driverHeader, by simpa [creationOperands] using hoperands⟩


@[expose]
def firstOrRoot (root : OperationPtr) : List OperationPtr → OperationPtr
  | [] => root
  | op :: _ => op

/-- Inserting a sequence before a root changes only the old predecessor's forward link. -/
theorem InsertBeforeChain.existing_next {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (rootIn : root.InBounds before.raw) (op : OperationPtr) (opIn : op.InBounds before.raw)
    (notInserted : op ∉ ops) :
    op.getNextOp! after.raw =
      if root.getPrevOp! before.raw = some op then some (firstOrRoot root ops)
      else op.getNextOp! before.raw := by
  induction chain with
  | nil =>
    simp only [firstOrRoot]
    split
    · rename_i hprev
      exact IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
        (missingUses := ∅) (missingSuccessorUses := ∅) rootIn (by grind) hprev
    · rfl
  | @cons before middle after rest newOp newIn rootIn' inserted tail ih =>
    have hne : op ≠ newOp := by intro h; subst op; simp at notInserted
    have hrootMiddle : root.InBounds middle.raw := by grind
    have hopMiddle : op.InBounds middle.raw := by grind
    have ht := ih hrootMiddle hopMiddle (fun hm => notInserted (List.mem_cons_of_mem _ hm))
    have hprev := root_prev_of_insertBefore (rootIn := rootIn') inserted
    have hn := OperationPtr.getNextOp!_wfRewriter_insertOp (operation := op) inserted
    rw [ht, hprev]
    simp only [Option.some.injEq, Ne.symm hne, ↓reduceIte]
    simpa [InsertPoint.prev!, hne, eq_comm, firstOrRoot] using hn

/-- An explicit forward chain ending at a possibly absent successor. -/
@[expose]
def ForwardChain (ctx : IRContext OpInfo) : List OperationPtr → Option OperationPtr → Prop
  | [], _ => True
  | op :: [], successor => op.getNextOp! ctx = successor
  | op :: next :: rest, successor => op.getNextOp! ctx = some next ∧ ForwardChain ctx (next :: rest) successor

/-- Returned operations occur in their supplied order immediately before the old root. -/
theorem InsertBeforeChain.forwardChain {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (rootIn : root.InBounds before.raw) (nodup : ops.Nodup) :
    ForwardChain after.raw ops (some root) := by
  induction chain with
  | nil => trivial
  | @cons before middle after rest newOp newIn rootIn' inserted tail ih =>
    have hrootMiddle : root.InBounds middle.raw := by grind
    have hnewMiddle : newOp.InBounds middle.raw := by grind
    have hne : newOp ∉ rest := (List.nodup_cons.mp nodup).1
    have hn := tail.existing_next hrootMiddle newOp hnewMiddle hne
    rw [root_prev_of_insertBefore (rootIn := rootIn') inserted] at hn
    simp only [↓reduceIte] at hn
    have ht := ih hrootMiddle (List.nodup_cons.mp nodup).2
    cases rest with
    | nil => exact hn
    | cons next rest => exact ⟨hn, ht⟩

/-- Every inserted operation obtains the same parent block as the old root. -/
theorem InsertBeforeChain.parents {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (nodup : ops.Nodup) (notRoot : root ∉ ops) :
    ∀ op ∈ ops, op.getParent! after.raw = root.getParent! before.raw := by
  induction chain with
  | nil => simp
  | @cons before middle after rest newOp newIn rootIn inserted tail ih =>
    have hrootNe : root ≠ newOp := by intro h; subst newOp; simp at notRoot
    have hrootParent := (operationHeaderPreserved_of_insertOp inserted hrootNe).parent
    have ht := ih (List.nodup_cons.mp nodup).2 (fun hm => notRoot (List.mem_cons_of_mem _ hm))
    intro op hm
    rcases List.mem_cons.mp hm with heq | hmem
    · subst op
      have hp := OperationPtr.getParent!_wfRewriter_insertOp (operation := newOp) inserted
      rw [(tail.preserves_header newOp (List.nodup_cons.mp nodup).1).parent]
      simpa [InsertPoint.block!] using hp
    · exact (ht op hmem).trans hrootParent


theorem ForwardChain.of_next_eq {before after : IRContext OpInfo}
    {ops : List OperationPtr} {successor : Option OperationPtr}
    (chain : ForwardChain before ops successor)
    (nextEq : ∀ op ∈ ops, op.getNextOp! after = op.getNextOp! before) :
    ForwardChain after ops successor := by
  induction ops with
  | nil => trivial
  | cons op rest ih =>
    cases rest with
    | nil => exact (nextEq op (by simp)).trans chain
    | cons next rest =>
      exact ⟨(nextEq op (by simp)).trans chain.1,
        ih chain.2 (fun other hm => nextEq other (List.mem_cons_of_mem _ hm))⟩

theorem ReplaceResultChain.preserves_next {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (op : OperationPtr) : op.getNextOp! after.raw = op.getNextOp! before.raw := by
  induction chain with
  | nil => rfl
  | cons value index different oldIn newIn tail ih => simpa using ih

theorem ForwardChain.erase_root {before : WfIRContext OpInfo} {root : OperationPtr}
    {regions : root.getNumRegions! before.raw = 0} {unused : !root.hasUses! before.raw}
    {rootIn : root.InBounds before.raw} {ops : List OperationPtr}
    (chain : ForwardChain before.raw ops (some root))
    (allIn : ∀ op ∈ ops, op.InBounds before.raw) (notRoot : root ∉ ops) :
    ForwardChain (WfRewriter.eraseOp before root regions unused rootIn).raw ops (root.getNextOp! before.raw) := by
  induction ops with
  | nil => trivial
  | cons op rest ih =>
    have opIn := allIn op (by simp)
    have hne : op ≠ root := by intro h; subst op; simp at notRoot
    have hafter : op.InBounds (WfRewriter.eraseOp before root regions unused rootIn).raw := by
      simpa [WfRewriter.eraseOp] using
        (Rewriter.eraseOp_inBounds (.operation op) hne).mpr opIn
    have hnext := OperationPtr.getNextOp!_wfRewriter_eraseOp hafter
    cases rest with
    | nil =>
      have hprev := IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some opIn
        (missingUses := ∅) (missingSuccessorUses := ∅) before.wellFormed chain
      simpa [ForwardChain, hprev] using hnext
    | cons next rest =>
      have hnotPrev : root.getPrevOp! before.raw ≠ some op := by
        intro hprev
        have hnextRoot := IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some rootIn
          (missingUses := ∅) (missingSuccessorUses := ∅) before.wellFormed hprev
        have heq : root = next := Option.some.inj (hnextRoot.symm.trans chain.1)
        subst next
        exact notRoot (by simp)
      refine ⟨?_, ih chain.2 (fun other hm => allIn other (List.mem_cons_of_mem _ hm))
        (fun hm => notRoot (List.mem_cons_of_mem _ hm))⟩
      simpa [Ne.symm hnotPrev, hne, chain.1] using hnext


/-- Surviving source operation pointers remain allocated after successful checked local rewriting. -/
theorem Pattern.fromLocalRewrite_existing_inBounds (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root) :
    op.InBounds result.ctx.raw := by
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [driverContext_eq_of_chains hinsert hreplace hroot hregions hunused] at hctx
  rw [hctx]
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hopCreated := hcreated.inBounds_mono (.operation op) opIn
  have hopReplaced := hreplace.inBounds op (hinsert.inBounds op hopCreated)
  simpa [WfRewriter.eraseOp] using
    (Rewriter.eraseOp_inBounds (.operation op) different).mpr hopReplaced

/-- Every surviving named module function keeps the same pointer, name, and module ownership. -/
theorem Pattern.fromLocalRewrite_topLevelFunc (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {function moduleOp : OperationPtr} {name : StringAttr}
    (functionIn : function.InBounds rewriter.ctx.raw) (different : function ≠ root)
    (source : function.IsTopLevelFuncWithName moduleOp rewriter.ctx.raw name) :
    function.InBounds result.ctx.raw ∧ function.IsTopLevelFuncWithName moduleOp result.ctx.raw name := by
  refine ⟨rule.fromLocalRewrite_existing_inBounds localRun run attached regions notOwn
    function functionIn different, ?_⟩
  have hframe := rule.fromLocalRewrite_existing_frame localRun run attached regions notOwn
    function functionIn different
  exact hframe.1.isTopLevelFuncWithName source


theorem root_ne_own_predecessor {before : WfIRContext OpInfo} {root : OperationPtr}
    (rootIn : root.InBounds before.raw) (attached : (root.getParent! before.raw).isSome = true) :
    root.getPrevOp! before.raw ≠ some root := by
  cases hp : root.getParent! before.raw with
  | none => simp [hp] at attached
  | some block =>
    obtain ⟨ops, hopChain⟩ := before.wellFormed.opChain block (by grind)
    exact BlockPtr.OpChain_prev_ne rootIn before.wellFormed hp hopChain

theorem InsertBeforeChain.root_next {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (rootIn : root.InBounds before.raw) (attached : (root.getParent! before.raw).isSome = true)
    (notInserted : root ∉ ops) : root.getNextOp! after.raw = root.getNextOp! before.raw := by
  simpa [root_ne_own_predecessor rootIn attached] using
    chain.existing_next rootIn root rootIn notInserted

/-- The inserted sequence is spliced through the erased root to its original successor. -/
theorem driver_forwardChain {created inserted replaced : WfIRContext OpInfo}
    {root : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootIn : root.InBounds created.raw) (attached : (root.getParent! created.raw).isSome = true)
    (opsIn : ∀ op ∈ newOps, op.InBounds created.raw) (nodup : newOps.toList.Nodup) (notRoot : root ∉ newOps)
    (rootInReplaced : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) :
    ForwardChain (driverContext created root newOps replacements).raw newOps.toList (root.getNextOp! created.raw) := by
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced regions unused]
  have hchain := insertions.forwardChain rootIn nodup
  have hreplaced := ForwardChain.of_next_eq hchain (fun op _ => substitutions.preserves_next op)
  have hfinal := ForwardChain.erase_root (regions := regions) (unused := unused)
    (rootIn := rootInReplaced) hreplaced
    (fun op hm => substitutions.inBounds op (insertions.inBounds op (opsIn op (by simpa using hm))))
    (by simpa using notRoot)
  rw [substitutions.preserves_next root, insertions.root_next rootIn attached (by simpa using notRoot)] at hfinal
  exact hfinal


/-- Actual returned operations form an ordered same-block splice ending at the old successor. -/
theorem Pattern.fromLocalRewrite_inserted_splice (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    ForwardChain result.ctx.raw newOps.toList (root.getNextOp! rewriter.ctx.raw) ∧
      ∀ op ∈ newOps, op.getParent! result.ctx.raw = root.getParent! rewriter.ctx.raw := by
  obtain ⟨fresh, nodup, detached⟩ := rule.interpret_structure localRun
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hrootFields := WfIRContext.WithCreatedOps.structural_fields hcreated root rootIn
  have rootInCreated := hcreated.inBounds_mono (.operation root) rootIn
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  constructor
  · have hchain := driver_forwardChain hinsert hreplace rootInCreated
      (by simpa [hrootFields.1] using attached) (fun op hm => (fresh op).mp hm |>.1)
      nodup (fun hm => (fresh root).mp hm |>.2 <| rootIn) hroot hregions hunused
    simpa [hctx, hrootFields.2.2.1] using hchain
  · intro op hm
    have hop := (fresh op).mp hm |>.1
    have hopReplaced := hreplace.inBounds op (hinsert.inBounds op hop)
    have hne : op ≠ root := by intro heq; subst op; exact ((fresh root).mp hm).2 rootIn
    rw [hctx, driverContext_eq_of_chains hinsert hreplace hroot hregions hunused,
      (operationHeaderPreserved_of_eraseOp hne hopReplaced).parent,
      (hreplace.preserves_header op).parent]
    exact (hinsert.parents nodup (by simpa using fun hm => ((fresh root).mp hm).2 rootIn) op
      (by simpa using hm)).trans hrootFields.1


theorem InsertBeforeChain.preserves_firstOp_of_prev {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (hasPrev : root.getPrevOp! before.raw ≠ none) (block : BlockPtr) :
    block.getFirstOp! after.raw = block.getFirstOp! before.raw := by
  induction chain with
  | nil => rfl
  | @cons before middle after rest newOp newIn rootIn inserted tail ih =>
    have hprev := root_prev_of_insertBefore (rootIn := rootIn) inserted
    rw [ih (by simp [hprev])]
    have hf := BlockPtr.getFirstOp!_wfRewriter_insertOp (block := block) inserted
    simpa [InsertPoint.prev!, hasPrev] using hf

theorem InsertBeforeChain.firstOp {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (block : BlockPtr) (blockIn : block.InBounds before.raw)
    (rootFirst : block.getFirstOp! before.raw = some root) :
    block.getFirstOp! after.raw = some (firstOrRoot root ops) := by
  cases chain with
  | nil => exact rootFirst
  | @cons before middle after rest newOp newIn rootIn inserted tail =>
    obtain ⟨oldOps, hchain⟩ := before.wellFormed.opChain block blockIn
    have hprev : root.getPrevOp! before.raw = none := hchain.prevFirst rootFirst
    have hparent : root.getParent! before.raw = some block := by grind
    have hmiddleFirst := BlockPtr.getFirstOp!_wfRewriter_insertOp (block := block) inserted
    have hmiddlePrev := root_prev_of_insertBefore (rootIn := rootIn) inserted
    rw [tail.preserves_firstOp_of_prev (by simp [hmiddlePrev])]
    simpa [InsertPoint.block!, InsertPoint.prev!, hparent, hprev, firstOrRoot] using hmiddleFirst

theorem ReplaceResultChain.genericInBounds {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (ptr : GenericPtr) (ptrIn : ptr.InBounds before.raw) : ptr.InBounds after.raw := by
  induction chain with
  | nil => exact ptrIn
  | cons value index different oldIn newIn tail ih => exact ih (by grind)

theorem ReplaceResultChain.preserves_firstOp {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (block : BlockPtr) : block.getFirstOp! after.raw = block.getFirstOp! before.raw := by
  induction chain with
  | nil => rfl
  | cons value index different oldIn newIn tail ih => simpa using ih

/-- A root at block entry is replaced by the first new operation, or by its old successor. -/
theorem driver_firstOp {created inserted replaced : WfIRContext OpInfo}
    {root : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootIn : root.InBounds created.raw) (attached : (root.getParent! created.raw).isSome = true)
    (notRoot : root ∉ newOps) (block : BlockPtr) (blockIn : block.InBounds created.raw)
    (rootFirst : block.getFirstOp! created.raw = some root)
    (rootInReplaced : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) :
    block.getFirstOp! (driverContext created root newOps replacements).raw =
      match newOps.toList with
      | [] => root.getNextOp! created.raw
      | op :: _ => some op := by
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced regions unused]
  have hfirst := (substitutions.preserves_firstOp block).trans (insertions.firstOp block blockIn rootFirst)
  have hblockIn : block.InBounds replaced.raw :=
    substitutions.genericInBounds (.block block) (insertions.genericInBounds (.block block) blockIn)
  have hnext := (substitutions.preserves_next root).trans
    (insertions.root_next rootIn attached (by simpa using notRoot))
  have herase := BlockPtr.getFirstOp!_wfRewriter_eraseOp (block := block)
    (ctx := replaced) (op := root) (opRegions := regions) (opUses := unused) (hOp := rootInReplaced)
  cases hlist : newOps.toList with
  | nil => simpa [hfirst, hlist, firstOrRoot, hblockIn, hnext] using herase
  | cons first rest =>
    have hne : first ≠ root := by
      intro heq; subst first
      apply notRoot
      have hm : root ∈ newOps.toList := by rw [hlist]; simp
      simpa only [Array.mem_toList_iff] using hm
    simpa [hfirst, hlist, firstOrRoot, hne] using herase


theorem InsertBeforeChain.root_prev_origin {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (op : OperationPtr) (previous : root.getPrevOp! after.raw = some op) :
    root.getPrevOp! before.raw = some op ∨ op ∈ ops := by
  induction chain with
  | nil => exact .inl previous
  | @cons before middle after rest newOp newIn rootIn inserted tail ih =>
    rcases ih previous with hmiddle | hrest
    · rw [root_prev_of_insertBefore (rootIn := rootIn) inserted] at hmiddle
      have heq := Option.some.inj hmiddle
      subst op
      exact .inr (by simp)
    · exact .inr (List.mem_cons_of_mem _ hrest)

theorem ReplaceResultChain.preserves_prev {root : OperationPtr} {replacements : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root replacements before after)
    (op : OperationPtr) : op.getPrevOp! after.raw = op.getPrevOp! before.raw := by
  induction chain with
  | nil => rfl
  | cons value index different oldIn newIn tail ih => simpa using ih

theorem driver_existing_next {created inserted replaced : WfIRContext OpInfo}
    {root : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootIn : root.InBounds created.raw) (op : OperationPtr) (opIn : op.InBounds created.raw)
    (different : op ≠ root) (notInserted : op ∉ newOps.toList)
    (notPredecessor : root.getPrevOp! created.raw ≠ some op)
    (rootInReplaced : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) :
    op.getNextOp! (driverContext created root newOps replacements).raw = op.getNextOp! created.raw := by
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced regions unused]
  have hopReplaced := substitutions.inBounds op (insertions.inBounds op opIn)
  have hopErased : op.InBounds (WfRewriter.eraseOp replaced root regions unused rootInReplaced).raw := by
    simpa [WfRewriter.eraseOp] using (Rewriter.eraseOp_inBounds (.operation op) different).mpr hopReplaced
  have hnotPrevReplaced : root.getPrevOp! replaced.raw ≠ some op := by
    rw [substitutions.preserves_prev root]
    intro hprev
    rcases insertions.root_prev_origin op hprev with horiginal | hnew
    · exact notPredecessor horiginal
    · exact notInserted hnew
  have hn := OperationPtr.getNextOp!_wfRewriter_eraseOp hopErased
  simp only [Ne.symm hnotPrevReplaced, different, ↓reduceIte] at hn
  rw [hn, substitutions.preserves_next op]
  simpa [notPredecessor] using insertions.existing_next rootIn op opIn notInserted


theorem WfIRContext.WithCreatedOps.preserves_block_first {before after : WfIRContext OpInfo}
    (created : WfIRContext.WithCreatedOps before after) (block : BlockPtr) :
    block.getFirstOp! after.raw = block.getFirstOp! before.raw := by
  induction created with
  | Nil => rfl
  | CreatedOp first middle last previous hcreate ih =>
    obtain ⟨code, types, operands, successors, regions, properties, h₁, h₂, h₃, h₄, hcreate⟩ := hcreate
    have hb : block.getFirstOp! last.raw = block.getFirstOp! middle.raw := by grind
    exact hb.trans ih

theorem Pattern.fromLocalRewrite_block_entry (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (block : BlockPtr) (blockIn : block.InBounds rewriter.ctx.raw)
    (rootFirst : block.getFirstOp! rewriter.ctx.raw = some root) :
    block.getFirstOp! result.ctx.raw =
      match newOps.toList with
      | [] => root.getNextOp! rewriter.ctx.raw
      | op :: _ => some op := by
  obtain ⟨fresh, _, _⟩ := rule.interpret_structure localRun
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hrootFields := WfIRContext.WithCreatedOps.structural_fields hcreated root rootIn
  have rootInCreated := hcreated.inBounds_mono (.operation root) rootIn
  have blockInCreated := hcreated.inBounds_mono (.block block) blockIn
  have hfirstCreated := (WfIRContext.WithCreatedOps.preserves_block_first hcreated block).trans rootFirst
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  have hfirst := driver_firstOp hinsert hreplace rootInCreated (by simpa [hrootFields.1] using attached)
    (fun hm => ((fresh root).mp hm).2 rootIn) block blockInCreated hfirstCreated hroot hregions hunused
  simpa [hctx, hrootFields.2.2.1] using hfirst

theorem driver_predecessor_splice {created inserted replaced : WfIRContext OpInfo}
    {root predecessor : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (rootIn : root.InBounds created.raw) (attached : (root.getParent! created.raw).isSome = true)
    (previous : root.getPrevOp! created.raw = some predecessor) (predecessorIn : predecessor.InBounds created.raw)
    (predecessorNotInserted : predecessor ∉ newOps.toList)
    (opsIn : ∀ op ∈ newOps, op.InBounds created.raw) (nodup : newOps.toList.Nodup) (notRoot : root ∉ newOps)
    (rootInReplaced : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) :
    ForwardChain (driverContext created root newOps replacements).raw (predecessor :: newOps.toList)
      (root.getNextOp! created.raw) := by
  have hn := insertions.existing_next rootIn predecessor predecessorIn predecessorNotInserted
  rw [previous] at hn
  simp only [↓reduceIte] at hn
  have hnewChain := insertions.forwardChain rootIn nodup
  have hchain : ForwardChain inserted.raw (predecessor :: newOps.toList) (some root) := by
    cases hlist : newOps.toList with
    | nil => simpa [ForwardChain, hlist, firstOrRoot] using hn
    | cons first rest => exact ⟨by simpa [hlist, firstOrRoot] using hn, by simpa [hlist] using hnewChain⟩
  have hreplaced := ForwardChain.of_next_eq hchain (fun op _ => substitutions.preserves_next op)
  have hpredNe : predecessor ≠ root := by
    intro heq; subst predecessor
    exact root_ne_own_predecessor rootIn attached previous
  have hnotMember : root ∉ predecessor :: newOps.toList := by
    simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm hpredNe, by simpa using notRoot⟩
  have hfinal := ForwardChain.erase_root (regions := regions) (unused := unused) (rootIn := rootInReplaced)
    hreplaced (fun op hm => by
      have hopCreated : op.InBounds created.raw := by
        rcases List.mem_cons.mp hm with heq | hnew
        · simpa [heq] using predecessorIn
        · exact opsIn op (by simpa using hnew)
      exact substitutions.inBounds op (insertions.inBounds op hopCreated)) hnotMember
  rw [substitutions.preserves_next root, insertions.root_next rootIn attached (by simpa using notRoot)] at hfinal
  simpa only [driverContext_eq_of_chains insertions substitutions rootInReplaced regions unused] using hfinal


theorem Pattern.fromLocalRewrite_predecessor_splice (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root predecessor : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (previous : root.getPrevOp! rewriter.ctx.raw = some predecessor) :
    ForwardChain result.ctx.raw (predecessor :: newOps.toList) (root.getNextOp! rewriter.ctx.raw) := by
  obtain ⟨fresh, nodup, _⟩ := rule.interpret_structure localRun
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hrootFields := WfIRContext.WithCreatedOps.structural_fields hcreated root rootIn
  have rootInCreated := hcreated.inBounds_mono (.operation root) rootIn
  have predecessorIn : predecessor.InBounds rewriter.ctx.raw := by grind
  have predecessorInCreated := hcreated.inBounds_mono (.operation predecessor) predecessorIn
  have notInserted : predecessor ∉ newOps.toList := by
    intro hm
    exact ((fresh predecessor).mp (by simpa using hm)).2 predecessorIn
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  have hchain := driver_predecessor_splice hinsert hreplace rootInCreated
    (by simpa [hrootFields.1] using attached) (hrootFields.2.1.trans previous) predecessorInCreated
    notInserted (fun op hm => (fresh op).mp hm |>.1) nodup
    (fun hm => ((fresh root).mp hm).2 rootIn) hroot hregions hunused
  simpa [hctx, hrootFields.2.2.1] using hchain

theorem Pattern.fromLocalRewrite_untouched_next (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root)
    (notPredecessor : root.getPrevOp! rewriter.ctx.raw ≠ some op) :
    op.getNextOp! result.ctx.raw = op.getNextOp! rewriter.ctx.raw := by
  obtain ⟨fresh, _, _⟩ := rule.interpret_structure localRun
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hrootFields := WfIRContext.WithCreatedOps.structural_fields hcreated root rootIn
  have hopFields := WfIRContext.WithCreatedOps.structural_fields hcreated op opIn
  have rootInCreated := hcreated.inBounds_mono (.operation root) rootIn
  have opInCreated := hcreated.inBounds_mono (.operation op) opIn
  have notInserted : op ∉ newOps.toList := by
    intro hm
    exact ((fresh op).mp (by simpa using hm)).2 opIn
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  have hnext := driver_existing_next hinsert hreplace rootInCreated op opInCreated different notInserted
    (by simpa [hrootFields.2.1] using notPredecessor) hroot hregions hunused
  simpa [hctx, hopFields.2.2.1] using hnext


theorem InsertBeforeChain.firstOp_of_not_root {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after)
    (rootIn : root.InBounds before.raw) (block : BlockPtr) (blockIn : block.InBounds before.raw)
    (notFirst : block.getFirstOp! before.raw ≠ some root) :
    block.getFirstOp! after.raw = block.getFirstOp! before.raw := by
  induction chain with
  | nil => rfl
  | @cons before middle after rest newOp newIn rootIn' inserted tail ih =>
    have hcond : ¬ (root.getParent! before.raw = some block ∧ root.getPrevOp! before.raw = none) := by
      intro h
      exact notFirst ((IRContext.WellFormed.firstOp!_eq_some_iff blockIn rootIn before.wellFormed).mpr h)
    have hfirst : block.getFirstOp! middle.raw = block.getFirstOp! before.raw := by
      simpa [InsertPoint.block!, InsertPoint.prev!, hcond] using
        BlockPtr.getFirstOp!_wfRewriter_insertOp (block := block) inserted
    have hrootMiddle : root.InBounds middle.raw := by grind
    have hblockMiddle : block.InBounds middle.raw := by grind
    exact (ih hrootMiddle hblockMiddle (by simpa [hfirst] using notFirst)).trans hfirst

theorem Pattern.fromLocalRewrite_other_block_entry (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (block : BlockPtr) (blockIn : block.InBounds rewriter.ctx.raw)
    (notFirst : block.getFirstOp! rewriter.ctx.raw ≠ some root) :
    block.getFirstOp! result.ctx.raw = block.getFirstOp! rewriter.ctx.raw := by
  have hcreated := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  have hfirstCreated := WfIRContext.WithCreatedOps.preserves_block_first hcreated block
  have rootInCreated := hcreated.inBounds_mono (.operation root) rootIn
  have blockInCreated := hcreated.inBounds_mono (.block block) blockIn
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hfirstInserted := hinsert.firstOp_of_not_root rootInCreated block blockInCreated
    (by simpa [hfirstCreated] using notFirst)
  have hfirstReplaced := (hreplace.preserves_firstOp block).trans (hfirstInserted.trans hfirstCreated)
  have hctx := fromLocalRewrite_ctx localRun run
  rw [hctx, driverContext_eq_of_chains hinsert hreplace hroot hregions hunused]
  have herase := BlockPtr.getFirstOp!_wfRewriter_eraseOp (block := block) (ctx := replaced)
    (op := root) (opRegions := hregions) (opUses := hunused) (hOp := hroot)
  simpa [hfirstReplaced, notFirst] using herase


/-- A valid pattern automatically satisfies the replacement exclusion required by the concrete
splice frame. Root SSA dominance is supplied by the surrounding verified function CFG. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_existing_frame {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root) :
    OperationHeaderPreserved rewriter.ctx.raw result.ctx.raw op ∧
      op.getOperands! result.ctx.raw =
        (op.getOperands! rewriter.ctx.raw).map (renameRootResults root replacements.zipIdx.toList) := by
  have contract := valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun
  exact rule.fromLocalRewrite_existing_frame localRun run attached regions contract.1 op opIn different


/-- Concrete successful application of a valid pattern preserves every surviving operation's
header and precisely splices the newly created list into the old forward chain. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_frame_and_splice {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0) :
    (∀ op, op.InBounds rewriter.ctx.raw → op ≠ root →
      OperationHeaderPreserved rewriter.ctx.raw result.ctx.raw op ∧
      op.getOperands! result.ctx.raw =
        (op.getOperands! rewriter.ctx.raw).map (renameRootResults root replacements.zipIdx.toList)) ∧
    ForwardChain result.ctx.raw newOps.toList (root.getNextOp! rewriter.ctx.raw) ∧
    (∀ op ∈ newOps, op.getParent! result.ctx.raw = root.getParent! rewriter.ctx.raw) := by
  have contract := valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun
  exact ⟨fun op opIn different => rule.fromLocalRewrite_existing_frame localRun run attached
    regions contract.1 op opIn different,
    rule.fromLocalRewrite_inserted_splice localRun run attached regions contract.1⟩


end

end Veir.Puddle
