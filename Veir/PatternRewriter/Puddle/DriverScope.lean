module

public import Veir.PatternRewriter.Puddle.DriverStructure
import all Veir.PatternRewriter.Puddle.DriverStructure
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Semantics
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.Dominance.Basic
import all Veir.IR.Basic

namespace Veir.Puddle
public section

theorem renameRootResults_eq_self {root : OperationPtr} {pairs : List (ValuePtr × Nat)}
    {value : ValuePtr} (different : ∀ pair ∈ pairs, value ≠ root.getResult pair.2) :
    renameRootResults root pairs value = value := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [renameRootResults, ite_eq_right (different pair (by simp))]
    exact ih (fun pair member => different pair (List.mem_cons_of_mem _ member))

theorem InsertBeforeChain.semantic_fields {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpCode} (chain : InsertBeforeChain root ops before after)
    (op : OperationPtr) :
    op.getOpType! after.raw = op.getOpType! before.raw ∧
    op.getResultTypes! after.raw = op.getResultTypes! before.raw ∧
    (∀ code : OpCode, op.getProperties! after.raw code = op.getProperties! before.raw code) := by
  induction chain with
  | nil => exact ⟨rfl, rfl, fun _ => rfl⟩
  | cons newOp newIn rootIn inserted tail ih =>
    exact ⟨ih.1.trans (OperationPtr.getOpType!_wfRewriter_insertOp inserted),
      ih.2.1.trans (OperationPtr.getResultTypes!_wfRewriter_insertOp inserted),
      fun code => (ih.2.2 code).trans (OperationPtr.getProperties!_wfRewriter_insertOp inserted)⟩

/-- The driver preserves all semantic fields of a newly inserted operation whose operands
exclude the old root result slots. Inserting the operation only changes its structural links. -/
theorem Pattern.fromLocalRewrite_created_fields (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    (op : OperationPtr) (member : op ∈ newOps)
    (operandsNotOwn : ∀ value ∈ op.getOperands! created.raw,
      ∀ index < root.getNumResults! rewriter.ctx.raw, (root.getResult index : ValuePtr) ≠ value) :
    op.InBounds result.ctx.raw ∧
    op.getOpType! result.ctx.raw = op.getOpType! created.raw ∧
    op.getResultTypes! result.ctx.raw = op.getResultTypes! created.raw ∧
    op.getOperands! result.ctx.raw = op.getOperands! created.raw ∧
    (∀ code : OpCode, op.getProperties! result.ctx.raw code = op.getProperties! created.raw code) := by
  obtain ⟨fresh, _, _⟩ := rule.interpret_structure localRun
  have opIn := ((fresh op).mp member).1
  have different : op ≠ root := by intro equal; subst op; exact ((fresh root).mp member).2 rootIn
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [hctx, driverContext_eq_of_chains hinsert hreplace hroot hregions hunused]
  have opReplaced := hreplace.inBounds op (hinsert.inBounds op opIn)
  have opErased : op.InBounds (WfRewriter.eraseOp replaced root hregions hunused hroot).raw := by
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (GenericPtr.operation op) different).mpr opReplaced
  have insertedFields := hinsert.semantic_fields op
  have replacedFields := hreplace.preserves_header op
  have arity := fromLocalRewrite_result_arity localRun run
  have oldNum : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    have header := (rule.interpret_preserves_existing_fields localRun root rootIn).1
    have h := congrArg Array.size header.resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using h
  refine ⟨opErased, ?_, ?_, ?_, ?_⟩
  · exact (OperationPtr.getOpType!_wfRewriter_eraseOp opErased).trans
      (replacedFields.opcode.trans insertedFields.1)
  · exact (OperationPtr.getResultTypes!_wfRewriter_eraseOp opErased).trans
      (replacedFields.resultTypes.trans insertedFields.2.1)
  · rw [OperationPtr.getOperands!_wfRewriter_eraseOp opErased,
      hreplace.operands op (hinsert.inBounds op opIn), hinsert.preserves_operands op]
    suffices h : (op.getOperands! created.raw).map (renameRootResults root replacements.zipIdx.toList) =
        (op.getOperands! created.raw).map id by simpa using h
    apply Array.map_congr_left
    intro value memberValue
    apply renameRootResults_eq_self
    intro pair pairMember equal
    have hm : pair ∈ replacements.toList.zipIdx := by simpa using pairMember
    have hi := List.snd_lt_of_mem_zipIdx hm
    exact operandsNotOwn value memberValue pair.2 (by simpa [arity, oldNum] using hi) equal.symm
  · intro code
    exact (OperationPtr.getProperties!_wfRewriter_eraseOp opErased).trans
      ((replacedFields.properties code).trans (insertedFields.2.2 code))


/-- The checked pattern language excludes old root-result operands automatically, so the raw
created-op semantics used by local soundness are exactly those executed after the driver splice. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_created_fields {rule : Pattern OpCode}
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
    (op : OperationPtr) (member : op ∈ newOps) :
    op.InBounds result.ctx.raw ∧
    op.getOpType! result.ctx.raw = op.getOpType! created.raw ∧
    op.getResultTypes! result.ctx.raw = op.getResultTypes! created.raw ∧
    op.getOperands! result.ctx.raw = op.getOperands! created.raw ∧
    (∀ code : OpCode, op.getProperties! result.ctx.raw code = op.getProperties! created.raw code) := by
  have contract := valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun
  have operands := valid.createdOperandScope_of_interpret ctxDom rootRooted rootRegion rootReachable
    rootIn localRun
  apply rule.fromLocalRewrite_created_fields localRun run attached regions contract.1 op member
  intro value memberValue index bound
  exact (operands op member value memberValue).notOwn rootRooted rootRegion rootSSA rootIn index bound


theorem renameRootResults_ne_of_replacements {root : OperationPtr} {pairs : List (ValuePtr × Nat)}
    {value bad : ValuePtr} (different : value ≠ bad)
    (noOwn : ∀ pair ∈ pairs, ∀ other ∈ pairs, pair.1 ≠ root.getResult other.2)
    (safe : ∀ pair ∈ pairs, value = root.getResult pair.2 → pair.1 ≠ bad) :
    renameRootResults root pairs value ≠ bad := by
  induction pairs with
  | nil => exact different
  | cons pair rest ih =>
    simp only [renameRootResults]
    by_cases same : value = root.getResult pair.2
    · rw [ite_eq_left same, renameRootResults_eq_self]
      · exact safe pair (by simp) same
      · intro other member
        exact noOwn pair (by simp) other (List.mem_cons_of_mem _ member)
    · rw [ite_eq_right same]
      exact ih
        (fun pair hp other ho => noOwn pair (List.mem_cons_of_mem _ hp) other (List.mem_cons_of_mem _ ho))
        (fun pair hp => safe pair (List.mem_cons_of_mem _ hp))

/-- A live old root result cannot be forwarded to an earlier producer's result while that
producer is executing: the two required dominance directions would form an SSA cycle. -/
theorem renameRootResults_not_result_of_scope
    {ctx : WfIRContext OpCode} {root op : OperationPtr} {values : Array ValuePtr} {value : ValuePtr}
    (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootSSA : region.hasSSADominance ctx) (rootReachable : root.HierarchicallyReachable ctx)
    (rootIn : root.InBounds ctx.raw) (_opIn : op.InBounds ctx.raw)
    (arity : values.size = root.getNumResults! ctx.raw)
    (scope : ∀ replacement ∈ values, ReplacementValueScope ctx root replacement)
    (live : value.DominatesIp (.before op) ctx)
    (notResult : value ∉ op.getResults! ctx.raw) :
    renameRootResults root values.zipIdx.toList value ∉ op.getResults! ctx.raw := by
  intro member
  obtain ⟨index, bound, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
  have badIn : (op.getResult index : ValuePtr).InBounds ctx.raw := by grind
  have pairFacts (pair : ValuePtr × Nat) (hp : pair ∈ values.zipIdx.toList) :
      pair.1 ∈ values ∧ pair.2 < root.getNumResults! ctx.raw := by
    have hp' : pair ∈ values.toList.zipIdx := by simpa using hp
    exact ⟨by simpa using List.fst_mem_of_mem_zipIdx hp',
      by simpa [← arity] using List.snd_lt_of_mem_zipIdx hp'⟩
  have hne : value ≠ (op.getResult index : ValuePtr) := by
    intro heq
    apply notResult
    subst value
    exact OperationPtr.getResults!.mem_iff_exists_index.mpr ⟨index, bound, rfl⟩
  apply (renameRootResults_ne_of_replacements (root := root) (pairs := values.zipIdx.toList) hne ?_ ?_) equal.symm
  · intro pair hp other ho
    exact Ne.symm ((scope pair.1 (pairFacts pair hp).1).notOwn rootRooted rootRegion rootSSA
      rootIn other.2 (pairFacts other ho).2)
  · intro pair hp original equalReplacement
    have replacementDom := (scope pair.1 (pairFacts pair hp).1).dominates_of_inBounds
      (by simpa [equalReplacement] using badIn)
    have backwards := (ValuePtr.DominatesIp.before_iff.mp replacementDom).2
    have forwards := (ValuePtr.DominatesIp.before_iff.mp live).2
    rw [original] at forwards
    rw [equalReplacement] at backwards
    have forwards' : root.ProperlyDominates op ctx false := by
      simpa [ValuePtr.ProperlyDominates] using forwards
    have backwards' : op.ProperlyDominates root ctx false := by
      simpa [ValuePtr.ProperlyDominates] using backwards
    exact OperationPtr.not_properlyDominates_self rootRooted rootRegion rootSSA
      (forwards'.trans_of_reachable_of_not_enclosing backwards' rootReachable)


/-- Scope after a surviving operation excludes aliasing its newly computed result vector,
even when the rewrite forwards root results to already dominating producer results. -/
theorem renameRootResults_not_result_after
    {ctx : WfIRContext OpCode} {root op : OperationPtr} {values : Array ValuePtr} {value : ValuePtr}
    (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootSSA : region.hasSSADominance ctx) (rootReachable : root.HierarchicallyReachable ctx)
    (rootIn : root.InBounds ctx.raw) (opIn : op.InBounds ctx.raw)
    (arity : values.size = root.getNumResults! ctx.raw)
    (scope : ∀ replacement ∈ values, ReplacementValueScope ctx root replacement)
    {block : BlockPtr} (opParent : op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some opRegion)
    (live : value.InScopeAt (.at (.after op ctx.raw block opParent opIn)) ctx)
    (notResult : value ∉ op.getResults! ctx.raw) :
    renameRootResults root values.zipIdx.toList value ∉ op.getResults! ctx.raw := by
  rw [ValuePtr.inScopeAt_at] at live
  have before : value.DominatesIp (.before op) ctx :=
    (ValuePtr.DominatesIp.after_iff blockParent).mp live |>.resolve_right notResult
  exact renameRootResults_not_result_of_scope rootRooted rootRegion rootSSA rootReachable rootIn opIn
    arity scope before notResult

/-- The source-only no-alias condition needed when committing an untouched operation's results
follows from the actual valid pattern/driver run and source SSA dominance. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_noAlias_after {rule : Pattern OpCode}
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
    {op : OperationPtr} (opIn : op.InBounds rewriter.ctx.raw)
    {block : BlockPtr} (opParent : op.getParent! rewriter.ctx.raw = some block)
    (blockParent : block.getParent! rewriter.ctx.raw = some opRegion) {value : ValuePtr}
    (live : value.InScopeAt (.at (.after op rewriter.ctx.raw block opParent opIn)) rewriter.ctx)
    (notResult : value ∉ op.getResults! rewriter.ctx.raw) :
    renameRootResults root replacements.zipIdx.toList value ∉ op.getResults! rewriter.ctx.raw := by
  have hnum : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    have ht := congrArg Array.size (rule.interpret_preserves_existing_fields localRun root rootIn).1.resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using ht
  exact renameRootResults_not_result_after rootRooted rootRegion rootSSA rootReachable rootIn opIn
    ((fromLocalRewrite_result_arity localRun run).trans hnum)
    (valid.replacementScope_of_interpret ctxDom rootRooted rootRegion rootReachable rootIn localRun)
    opParent blockParent live notResult


theorem Pattern.fromLocalRewrite_replacementsInBounds (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    ∀ value ∈ replacements, value.InBounds result.ctx.raw := by
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [hctx, driverContext_eq_of_chains hinsert hreplace hroot hregions hunused]
  have hnum : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    have ht := congrArg Array.size (rule.interpret_preserves_existing_fields localRun root rootIn).1.resultTypes
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using ht
  intro value member
  have valueCreated := rule.interpret_returnValuesInBounds_of_root rootIn localRun value member
  have valueReplaced := hreplace.genericInBounds (.value value)
    (hinsert.genericInBounds (.value value) valueCreated)
  have different : match value with
      | .opResult res => res.op ≠ root
      | .blockArgument _ => True := by
    cases value with
    | blockArgument arg => trivial
    | opResult res =>
      intro same
      have indexBound : res.index < root.getNumResults! rewriter.ctx.raw := by grind
      have equal : (root.getResult res.index : ValuePtr) = .opResult res :=
        congrArg ValuePtr.opResult (OperationPtr.eq_getResult_of_OpResultPtr_op_eq same).symm
      exact notOwn (.opResult res) member res.index indexBound equal
  simpa [WfRewriter.eraseOp] using
    (Rewriter.eraseOp_inBounds (op := root) (GenericPtr.value value)
      (by cases value <;> simp_all)).mpr valueReplaced

theorem CTree.Pattern.Valid.fromLocalRewrite_replacementsInBounds {rule : Pattern OpCode}
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
    ∀ value ∈ replacements, value.InBounds result.ctx.raw := by
  exact rule.fromLocalRewrite_replacementsInBounds localRun run attached regions
    (valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA rootReachable rootIn localRun).1


theorem CTree.Pattern.Valid.fromLocalRewrite_created_nonterminator {rule : Pattern OpCode}
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
    ∀ op ∈ newOps, HasOpInfo.isTerminator (op.getOpType! result.ctx.raw) = false := by
  intro op member
  have fields := valid.fromLocalRewrite_created_fields ctxDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions op member
  rw [fields.2.1]
  exact valid.created_nonterminator_of_interpret localRun op member


/-- Every old SSA pointer except the erased root's results survives the concrete driver. -/
theorem Pattern.fromLocalRewrite_survivingValueInBounds (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {value : ValuePtr} (valueIn : value.InBounds rewriter.ctx.raw)
    (notResult : value ∉ root.getResults! rewriter.ctx.raw) : value.InBounds result.ctx.raw := by
  obtain ⟨inserted, replaced, hinsert, hreplace, hroot, hregions, hunused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [hctx, driverContext_eq_of_chains hinsert hreplace hroot hregions hunused]
  have valueCreated := (rule.interpret_returnCtxChanges _ _ _ _ _ localRun).inBounds_mono (.value value) valueIn
  have valueReplaced := hreplace.genericInBounds (.value value)
    (hinsert.genericInBounds (.value value) valueCreated)
  have different : match value with
      | .opResult res => res.op ≠ root
      | .blockArgument _ => True := by
    cases value with
    | blockArgument arg => trivial
    | opResult res =>
      intro same
      apply notResult
      apply OperationPtr.getResults!.mem_iff_exists_index.mpr
      exact ⟨res.index, by grind,
        congrArg ValuePtr.opResult (OperationPtr.eq_getResult_of_OpResultPtr_op_eq same).symm⟩
  simpa [WfRewriter.eraseOp] using
    (Rewriter.eraseOp_inBounds (op := root) (GenericPtr.value value)
      (by cases value <;> simp_all)).mpr valueReplaced

/-- An explicit source-to-final SSA mapping for a single root replacement. -/
def rootValueMapping {source target : WfIRContext OpCode} (root : OperationPtr)
    (values : Array ValuePtr) (arity : values.size = root.getNumResults! source.raw)
    (valuesIn : ∀ value ∈ values, value.InBounds target.raw)
    (surviving : ∀ value, value.InBounds source.raw → value ∉ root.getResults! source.raw →
      value.InBounds target.raw) : ValueMapping source target :=
  fun ⟨value, valueIn⟩ =>
    if own : value ∈ root.getResults! source.raw then
      ⟨values[(root.getResults! source.raw).idxOf value]!, by
        apply valuesIn
        have indexBound : (root.getResults! source.raw).idxOf value < values.size := by
          have indexBound := Array.idxOf_lt_size_iff.mpr own
          simpa [arity] using indexBound
        rw [getElem!_pos values _ indexBound]
        exact Array.getElem_mem indexBound⟩
    else ⟨value, surviving value valueIn own⟩

/-- Runtime arity checking and checked splice safety make the final SSA mapping concrete. -/
def Pattern.fromLocalRewrite_mapping (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) : ValueMapping rewriter.ctx result.ctx :=
  rootValueMapping root replacements (by
    have hnum := congrArg Array.size (rule.interpret_preserves_existing_fields localRun root rootIn).1.resultTypes
    have arity := fromLocalRewrite_result_arity localRun run
    simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!] at hnum
    exact arity.trans hnum)
    (rule.fromLocalRewrite_replacementsInBounds localRun run attached regions notOwn)
    (fun _ hin hnot => rule.fromLocalRewrite_survivingValueInBounds localRun run attached regions notOwn hin hnot)


theorem rootValueMapping_of_notResult {source target : WfIRContext OpCode} (root : OperationPtr)
    (values : Array ValuePtr) (arity valuesIn surviving) {value : ValuePtr} (valueIn : value.InBounds source.raw)
    (notOwn : value ∉ root.getResults! source.raw) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving ⟨value, valueIn⟩).val = value := by
  simp [rootValueMapping, notOwn]

theorem rootValueMapping_getResult {source target : WfIRContext OpCode} (root : OperationPtr)
    (rootIn : root.InBounds source.raw) (values : Array ValuePtr) (arity valuesIn surviving)
    (index : Nat) (bound : index < root.getNumResults! source.raw) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving
      ⟨root.getResult index, by grind⟩).val = values[index]! := by
  have member := OperationPtr.getResults!.mem_getResult (op := root) (ctx := source.raw) bound
  have eq := OperationPtr.getResult_eq_of_idxOf_getResults! member rfl
  have indexEq : (root.getResults! source.raw).idxOf (root.getResult index : ValuePtr) = index := by
    have h := congrArg (fun v : ValuePtr => match v with | .opResult result => result.index | _ => 0) eq
    simpa only [OperationPtr.getResult_index] using h
  simp [rootValueMapping, member, indexEq]

theorem rootValueMapping_results {source target : WfIRContext OpCode} (root : OperationPtr)
    (rootIn : root.InBounds source.raw) (values : Array ValuePtr) (arity valuesIn surviving) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving).applyToArray
      (root.getResults! source.raw) = values := by
  apply Array.ext
  · simp [ValueMapping.applyToArray, arity]
  · intro i hi hj
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach]
    have hb : i < root.getNumResults! source.raw := by simpa [ValueMapping.applyToArray] using hi
    have hresult := rootValueMapping_getResult (source := source) (target := target) root rootIn values arity valuesIn surviving i hb
    simpa [OperationPtr.getResults!.getElem_eq_getResult hb, getElem!_pos values i hj] using hresult

theorem renameRootResults_eq_of_member {root : OperationPtr} {pairs : List (ValuePtr × Nat)}
    {index : Nat} {replacement : ValuePtr}
    (member : (replacement, index) ∈ pairs)
    (unique : ∀ pair ∈ pairs, pair.2 = index → pair.1 = replacement)
    (noOwn : ∀ pair ∈ pairs, replacement ≠ root.getResult pair.2) :
    renameRootResults root pairs (root.getResult index) = replacement := by
  induction pairs with
  | nil => simp at member
  | cons first rest ih =>
    simp only [renameRootResults]
    by_cases same : first.2 = index
    · have hv := unique first (by simp) same
      have heq : (root.getResult index : ValuePtr) = root.getResult first.2 := by rw [same]
      rw [ite_eq_left heq, hv]
      exact renameRootResults_eq_self (fun pair hp => noOwn pair (List.mem_cons_of_mem _ hp))
    · have heq : (root.getResult index : ValuePtr) ≠ root.getResult first.2 := by
        intro equal
        apply same
        have h := congrArg (fun v : ValuePtr => match v with | .opResult result => result.index | _ => 0) equal
        simpa only [OperationPtr.getResult_index] using h.symm
      rw [ite_eq_right heq]
      apply ih
      · simp only [List.mem_cons] at member
        rcases member with head | tail
        · cases head
          exact False.elim (same rfl)
        · exact tail
      · exact fun pair hp => unique pair (List.mem_cons_of_mem _ hp)
      · exact fun pair hp => noOwn pair (List.mem_cons_of_mem _ hp)


theorem rootValueMapping_eq_renameRootResults {source target : WfIRContext OpCode} (root : OperationPtr)
    (rootIn : root.InBounds source.raw) (values : Array ValuePtr) (arity valuesIn surviving)
    (notOwn : ∀ value ∈ values, ∀ index < root.getNumResults! source.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {value : ValuePtr} (valueIn : value.InBounds source.raw) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving
      ⟨value, valueIn⟩).val = renameRootResults root values.zipIdx.toList value := by
  by_cases own : value ∈ root.getResults! source.raw
  · obtain ⟨index, bound, rfl⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp own
    rw [rootValueMapping_getResult root rootIn values arity valuesIn surviving index bound]
    symm
    apply renameRootResults_eq_of_member
    · simp only [Array.mem_toList_iff, Array.mk_mem_zipIdx_iff_getElem?]
      have hb : index < values.size := by omega
      simp [getElem?_pos values index hb, getElem!_pos values index hb]
    · intro pair member same
      have hp := Array.mem_zipIdx' (xs := values) (x := pair.1) (i := pair.2)
        (by simpa only [Array.mem_toList_iff] using member)
      simpa [same, getElem!_pos values index (by omega)] using hp.2
    · intro pair member equal
      have hp := Array.mem_zipIdx' (xs := values) (x := pair.1) (i := pair.2)
        (by simpa only [Array.mem_toList_iff] using member)
      have hmem : values[index]! ∈ values := by
        rw [getElem!_pos values index (by omega)]
        exact Array.getElem_mem (by omega)
      exact notOwn _ hmem pair.2 (by omega) equal.symm
  · rw [rootValueMapping_of_notResult root values arity valuesIn surviving valueIn own]
    symm
    apply renameRootResults_eq_self
    intro pair member equal
    have hp := Array.mem_zipIdx' (xs := values) (x := pair.1) (i := pair.2)
        (by simpa only [Array.mem_toList_iff] using member)
    apply own
    rw [equal]
    exact OperationPtr.getResults!.mem_getResult (by omega)


theorem rootValueMapping_other_results {source target : WfIRContext OpCode} (root : OperationPtr)
    (values : Array ValuePtr) (arity valuesIn surviving) {op : OperationPtr}
    (_opIn : op.InBounds source.raw) (different : op ≠ root) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving).applyToArray
      (op.getResults! source.raw) = op.getResults! source.raw := by
  apply Array.ext
  · simp [ValueMapping.applyToArray]
  · intro i hi hj
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach]
    apply rootValueMapping_of_notResult
    intro member
    have hi' : i < op.getNumResults! source.raw := by simpa using hj
    rw [OperationPtr.getResults!.getElem_eq_getResult hi'] at member
    obtain ⟨index, _, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have heq := congrArg (fun v : ValuePtr => match v with | .opResult res => some res.op | _ => none) equal
    exact different (by simpa only [OperationPtr.getResult_op, Option.some.injEq] using heq.symm)

/-- Exact equations for the canonical driver mapping, independent of existential witness choice. -/
theorem Pattern.fromLocalRewrite_mapping_properties (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    let mapping := rule.fromLocalRewrite_mapping localRun run attached regions notOwn
    mapping.applyToArray (root.getResults! rewriter.ctx.raw) = replacements ∧
    (∀ value valueIn, (mapping ⟨value, valueIn⟩).val =
      renameRootResults root replacements.zipIdx.toList value) ∧
    (∀ op, ∀ _opIn : op.InBounds rewriter.ctx.raw, op ≠ root →
      mapping.applyToArray (op.getResults! rewriter.ctx.raw) = op.getResults! rewriter.ctx.raw) := by
  refine ⟨?_, ?_, ?_⟩
  · exact rootValueMapping_results root rootIn _ _ _ _
  · intro value valueIn
    exact rootValueMapping_eq_renameRootResults root rootIn _ _ _ _ notOwn valueIn
  · intro op opIn different
    exact rootValueMapping_other_results root _ _ _ _ opIn different

/-- A packaged concrete final mapping and the exact vector/root-renaming equations used by CFG
simulation. All pointer bounds come from the successful driver, rather than external hypotheses. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_mapping_exists {rule : Pattern OpCode}
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
    ∃ mapping : ValueMapping rewriter.ctx result.ctx,
      mapping.applyToArray (root.getResults! rewriter.ctx.raw) = replacements ∧
      (∀ value valueIn, (mapping ⟨value, valueIn⟩).val =
        renameRootResults root replacements.zipIdx.toList value) ∧
      (∀ op, ∀ _opIn : op.InBounds rewriter.ctx.raw, op ≠ root →
        mapping.applyToArray (op.getResults! rewriter.ctx.raw) = op.getResults! rewriter.ctx.raw) := by
  have notOwn := (valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun).1
  exact ⟨rule.fromLocalRewrite_mapping localRun run attached regions notOwn,
    rule.fromLocalRewrite_mapping_properties localRun run attached regions notOwn⟩


/-- Live source values outside incoming arguments cannot be renamed onto those arguments.
The only possible alias would require an incoming argument to dominate the root while the root
simultaneously dominates that argument's block entry, which SSA dominance excludes. -/
theorem renameRootResults_not_argument_of_scope
    {ctx : WfIRContext OpCode} {root : OperationPtr} {block : BlockPtr}
    {values : Array ValuePtr} {value : ValuePtr}
    (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region)
    (rootSSA : region.hasSSADominance ctx) (rootIn : root.InBounds ctx.raw)
    (blockIn : block.InBounds ctx.raw) (blockRooted : block.RootedAt irRoot ctx)
    (blockReachable : block.LocallyReachable blockRegion ctx)
    (blockSSA : blockRegion.hasSSADominance ctx)
    (arity : values.size = root.getNumResults! ctx.raw)
    (scope : ∀ replacement ∈ values, ReplacementValueScope ctx root replacement)
    (live : value.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx)
    (notArgument : value ∉ block.getArguments! ctx.raw) :
    renameRootResults root values.zipIdx.toList value ∉ block.getArguments! ctx.raw := by
  intro member
  obtain ⟨index, bound, equal⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
  have badIn : (block.getArgument index : ValuePtr).InBounds ctx.raw := by grind
  have pairFacts (pair : ValuePtr × Nat) (hp : pair ∈ values.zipIdx.toList) :
      pair.1 ∈ values ∧ pair.2 < root.getNumResults! ctx.raw := by
    have hp' : pair ∈ values.toList.zipIdx := by simpa using hp
    exact ⟨by simpa using List.fst_mem_of_mem_zipIdx hp',
      by simpa [← arity] using List.snd_lt_of_mem_zipIdx hp'⟩
  have different : value ≠ (block.getArgument index : ValuePtr) := by
    intro equalValue
    apply notArgument
    rw [equalValue]
    exact BlockPtr.getArguments!.mem_iff_exists_index.mpr ⟨index, bound, rfl⟩
  apply (renameRootResults_ne_of_replacements (root := root) (pairs := values.zipIdx.toList)
    different ?_ ?_) equal.symm
  · intro pair hp other ho
    exact Ne.symm ((scope pair.1 (pairFacts pair hp).1).notOwn rootRooted rootRegion rootSSA
      rootIn other.2 (pairFacts other ho).2)
  · intro pair hp original replacementEq
    have replacementDom := (scope pair.1 (pairFacts pair hp).1).dominates_of_inBounds
      (by simpa [replacementEq] using badIn)
    have rootDom : root.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx := by
      rw [original] at live
      cases live with
      | OpResult _ dominance => simpa only [OperationPtr.getResult_op] using dominance
    have argumentMember : pair.1 ∈ block.getArguments! ctx.raw := by
      rw [replacementEq]
      exact BlockPtr.getArguments!.mem_iff_exists_index.mpr ⟨index, bound, rfl⟩
    exact OperationPtr.DominatesIp.not_dominatesIp_before_of_mem_arguments blockSSA blockRooted
      blockReachable rootDom argumentMember replacementDom

/-- Root renaming fixes every original block argument vector. -/
theorem rootValueMapping_arguments {source target : WfIRContext OpCode} (root : OperationPtr)
    (values : Array ValuePtr) (arity valuesIn surviving) {block : BlockPtr}
    (_blockIn : block.InBounds source.raw) :
    (rootValueMapping (source := source) (target := target) root values arity valuesIn surviving).applyToArray
      (block.getArguments! source.raw) = block.getArguments! source.raw := by
  apply Array.ext
  · simp [ValueMapping.applyToArray]
  · intro i hi hj
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach]
    apply rootValueMapping_of_notResult
    intro member
    have hi' : i < block.getNumArguments! source.raw := by simpa using hj
    rw [BlockPtr.getArguments!.getElem_eq_getArgument hi'] at member
    obtain ⟨index, _, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    cases equal


theorem Pattern.fromLocalRewrite_mapping_arguments (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {block : BlockPtr} (blockIn : block.InBounds rewriter.ctx.raw) :
    (rule.fromLocalRewrite_mapping localRun run attached regions notOwn).applyToArray
      (block.getArguments! rewriter.ctx.raw) = block.getArguments! rewriter.ctx.raw := by
  exact rootValueMapping_arguments root _ _ _ _ blockIn

theorem CTree.Pattern.Valid.fromLocalRewrite_mapping_noAlias_arguments {rule : Pattern OpCode}
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
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {block : BlockPtr} (blockIn : block.InBounds rewriter.ctx.raw)
    (blockRooted : block.RootedAt irRoot rewriter.ctx)
    (blockReachable : block.LocallyReachable blockRegion rewriter.ctx)
    (blockSSA : blockRegion.hasSSADominance rewriter.ctx)
    (arguments : block.getArguments! result.ctx.raw = block.getArguments! rewriter.ctx.raw)
    {value : ValuePtr} (valueIn : value.InBounds rewriter.ctx.raw)
    (live : value.DominatesIp (InsertPoint.atStart! block rewriter.ctx.raw) rewriter.ctx)
    (notArgument : value ∉ block.getArguments! rewriter.ctx.raw) :
    ((rule.fromLocalRewrite_mapping localRun run attached regions notOwn) ⟨value, valueIn⟩).val ∉
      block.getArguments! result.ctx.raw := by
  have properties := rule.fromLocalRewrite_mapping_properties localRun run attached regions notOwn
  rw [properties.2.1 value valueIn, arguments]
  have arity : replacements.size = root.getNumResults! rewriter.ctx.raw := by
    have hnum := congrArg Array.size (rule.interpret_preserves_existing_fields localRun root rootIn).1.resultTypes
    simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!] at hnum
    exact (fromLocalRewrite_result_arity localRun run).trans hnum
  exact renameRootResults_not_argument_of_scope rootRooted rootRegion rootSSA rootIn blockIn
    blockRooted blockReachable blockSSA arity
    (valid.replacementScope_of_interpret ctxDom rootRooted rootRegion rootReachable rootIn localRun)
    live notArgument

end
end Veir.Puddle
