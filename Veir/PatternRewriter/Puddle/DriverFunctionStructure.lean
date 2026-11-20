module
public import Veir.PatternRewriter.Puddle.DriverStructure
public import Veir.Interfaces.FunctionInterfaces
import all Veir.PatternRewriter.Puddle.DriverStructure
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.CreationStructure
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo

namespace Veir.Puddle
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Local operation rewriting does not change region or block ownership, block chains,
or block-argument identities and types. Operation chains are handled separately. -/
structure RegionBlockHeadersPreserved (before after : IRContext OpInfo) : Prop where
  regionParent : ∀ region : RegionPtr, region.getParent! after = region.getParent! before
  firstBlock : ∀ region : RegionPtr, region.getFirstBlock! after = region.getFirstBlock! before
  lastBlock : ∀ region : RegionPtr, region.getLastBlock! after = region.getLastBlock! before
  blockParent : ∀ block : BlockPtr, block.getParent! after = block.getParent! before
  nextBlock : ∀ block : BlockPtr, block.getNextBlock! after = block.getNextBlock! before
  prevBlock : ∀ block : BlockPtr, block.getPrevBlock! after = block.getPrevBlock! before
  argumentTypes : ∀ block : BlockPtr, block.getArgumentTypes! after = block.getArgumentTypes! before
  arguments : ∀ block : BlockPtr, block.getArguments! after = block.getArguments! before

theorem RegionBlockHeadersPreserved.refl (ctx : IRContext OpInfo) :
    RegionBlockHeadersPreserved ctx ctx := by constructor <;> intros <;> rfl

theorem RegionBlockHeadersPreserved.trans {a b c : IRContext OpInfo}
    (hab : RegionBlockHeadersPreserved a b) (hbc : RegionBlockHeadersPreserved b c) :
    RegionBlockHeadersPreserved a c := by
  exact ⟨fun r => (hbc.regionParent r).trans (hab.regionParent r),
    fun r => (hbc.firstBlock r).trans (hab.firstBlock r),
    fun r => (hbc.lastBlock r).trans (hab.lastBlock r),
    fun b => (hbc.blockParent b).trans (hab.blockParent b),
    fun b => (hbc.nextBlock b).trans (hab.nextBlock b),
    fun b => (hbc.prevBlock b).trans (hab.prevBlock b),
    fun b => (hbc.argumentTypes b).trans (hab.argumentTypes b),
    fun b => (hbc.arguments b).trans (hab.arguments b)⟩

/-- Empty-region allocation creates no region or block headers. -/
theorem regionBlockHeadersPreserved_createOp {ctx : WfIRContext OpInfo}
    (code : OpInfo) (types : Array TypeAttr) (operands : Array ValuePtr) (properties : propertiesOf code)
    (operandBounds : ∀ value ∈ operands, value.InBounds ctx.raw)
    {after : WfIRContext OpInfo} {op : OperationPtr}
    (created : WfRewriter.createOp ctx code types operands #[] #[] properties none operandBounds = some (after, op)) :
    RegionBlockHeadersPreserved ctx.raw after.raw := by
  constructor <;> intros <;> try grind
  rename_i block
  apply Array.ext
  · grind
  · intro index left right
    have hv := ValuePtr.getType!_WfRewriter_createOp
      (value := .blockArgument (block.getArgument index)) created
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind),
      BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind)]
    exact hv

theorem CreateDecl.run_regionBlockHeaders (decl : CreateDecl OpInfo)
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : decl.run a ctx = some (newCtx, newOps, b)) :
    RegionBlockHeadersPreserved ctx.raw newCtx.raw := by
  cases decl with
  | operation code operandHandles typeHandles propertyHandle opHandle resultHandles =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨operands, hop, types, hty, properties, hprop, u, hguard, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨createdCtx, op⟩, hcreate, bound, hbindop, final, hbindresults, heq⟩ := h
      cases heq
      exact regionBlockHeadersPreserved_createOp code types operands properties _ hcreate
    · contradiction
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, heq⟩ := h
    cases heq
    exact .refl _
  | property code value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, heq⟩ := h
    cases heq
    exact .refl _
  | applyNative inputs rewrite outputs =>
    simp only [CreateDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨_, _, _, _, _, _, heq⟩ := h
    cases heq
    exact .refl _

theorem CreateProg.runDecls_regionBlockHeaders (decls : List (CreateDecl OpInfo))
    {ctx newCtx : WfIRContext OpInfo} {a b : Assignment OpInfo} {newOps : Array OperationPtr}
    (h : CreateProg.runDecls decls ctx a = some (newCtx, newOps, b)) :
    RegionBlockHeadersPreserved ctx.raw newCtx.raw := by
  induction decls generalizing ctx a newOps with
  | nil => cases h; exact .refl _
  | cons decl decls ih =>
    simp only [CreateProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middleCtx, created, middle⟩, hd, ⟨finalCtx, restOps, final⟩, hr, heq⟩ := h
    cases heq
    exact (decl.run_regionBlockHeaders hd).trans (ih hr)

theorem Pattern.interpret_regionBlockHeaders (rule : Pattern OpCode)
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : rule.interpret ctx root = some (newCtx, some (newOps, newValues))) :
    RegionBlockHeadersPreserved ctx.raw newCtx.raw := by
  unfold Pattern.interpret at h
  split at h
  · simp_all
  · split at h
    · contradiction
    · rename_i matched hmatch createdCtx createdOps finalAssignment hcreate
      split at h
      · contradiction
      · cases h
        exact CreateProg.runDecls_regionBlockHeaders _ hcreate

theorem regionBlockHeadersPreserved_insertOp {before after : WfIRContext OpInfo}
    {op : OperationPtr} {ip : InsertPoint} {opIn : op.InBounds before.raw} {ipIn : ip.InBounds before.raw}
    (inserted : WfRewriter.insertOp before op ip opIn ipIn = some after) :
    RegionBlockHeadersPreserved before.raw after.raw := by
  constructor <;> intros <;> try grind
  rename_i block
  apply Array.ext
  · grind
  · intro index left right
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind),
      BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind)]
    exact ValuePtr.getType!_wfRewriter_insertOp (value := .blockArgument (block.getArgument index)) inserted

theorem regionBlockHeadersPreserved_replaceValue {before : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} {different : oldValue ≠ newValue}
    {oldIn : oldValue.InBounds before.raw} {newIn : newValue.InBounds before.raw} :
    RegionBlockHeadersPreserved before.raw
      (WfRewriter.replaceValue before oldValue newValue different oldIn newIn).raw := by
  constructor <;> intros <;> try grind
  rename_i block
  apply Array.ext
  · grind
  · intro index left right
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind),
      BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind)]
    exact ValuePtr.getType!_WfRewriter_replaceValue (ctx := before) (value := .blockArgument (block.getArgument index))

theorem regionBlockHeadersPreserved_eraseOp {before : WfIRContext OpInfo}
    {root : OperationPtr} {regions : root.getNumRegions! before.raw = 0}
    {unused : !root.hasUses! before.raw} {rootIn : root.InBounds before.raw} :
    RegionBlockHeadersPreserved before.raw (WfRewriter.eraseOp before root regions unused rootIn).raw := by
  constructor <;> intros <;> try grind
  rename_i block
  apply Array.ext
  · grind
  · intro index left right
    rw [BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind),
      BlockPtr.getArgumentTypes!.getElem_eq_getArgument (by grind)]
    have afterBlock : block.InBounds (WfRewriter.eraseOp before root regions unused rootIn).raw := by
      apply Classical.byContradiction
      intro missing
      simp [BlockPtr.getArgumentTypes!, BlockPtr.get!_of_not_inBounds missing, Block.default_arguments_eq] at left
    have afterIndex : index < block.getNumArguments! (WfRewriter.eraseOp before root regions unused rootIn).raw := by grind
    exact ValuePtr.getType!_wfRewriter_eraseOp (ctx := before) (op := root)
      (value := .blockArgument (block.getArgument index))
      (by grind [ValuePtr.InBounds, BlockArgumentPtr.InBounds, BlockPtr.getArgument, BlockPtr.getNumArguments!, BlockPtr.getNumArguments])

theorem InsertBeforeChain.regionBlockHeaders {root : OperationPtr} {ops : List OperationPtr}
    {before after : WfIRContext OpInfo} (chain : InsertBeforeChain root ops before after) :
    RegionBlockHeadersPreserved before.raw after.raw := by
  induction chain with
  | nil => exact .refl _
  | cons op opIn rootIn inserted tail ih =>
      exact (regionBlockHeadersPreserved_insertOp inserted).trans ih

theorem ReplaceResultChain.regionBlockHeaders {root : OperationPtr} {values : List (ValuePtr × Nat)}
    {before after : WfIRContext OpInfo} (chain : ReplaceResultChain root values before after) :
    RegionBlockHeadersPreserved before.raw after.raw := by
  induction chain with
  | nil => exact .refl _
  | cons value index different oldIn newIn tail ih =>
      exact regionBlockHeadersPreserved_replaceValue.trans ih

/-- The successful concrete driver preserves all region/block headers from the original model. -/
theorem Pattern.fromLocalRewrite_regionBlockHeaders (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    RegionBlockHeadersPreserved rewriter.ctx.raw result.ctx.raw := by
  obtain ⟨inserted, replaced, insertions, substitutions, rootInReplaced, noRegions, unused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced noRegions unused] at hctx
  rw [hctx]
  exact (rule.interpret_regionBlockHeaders localRun).trans
    (insertions.regionBlockHeaders.trans (substitutions.regionBlockHeaders.trans regionBlockHeadersPreserved_eraseOp))

/-- Region and block pointers survive an operation-only driver rewrite. -/
theorem Pattern.fromLocalRewrite_region_block_inBounds (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) :
    (∀ region : RegionPtr, region.InBounds rewriter.ctx.raw → region.InBounds result.ctx.raw) ∧
    (∀ block : BlockPtr, block.InBounds rewriter.ctx.raw → block.InBounds result.ctx.raw) := by
  obtain ⟨inserted, replaced, insertions, substitutions, rootInReplaced, noRegions, unused⟩ :=
    rule.fromLocalRewrite_safe_phases localRun run attached regions notOwn
  have hctx := fromLocalRewrite_ctx localRun run
  rw [driverContext_eq_of_chains insertions substitutions rootInReplaced noRegions unused] at hctx
  rw [hctx]
  have createdOps := rule.interpret_returnCtxChanges _ _ _ _ _ localRun
  constructor <;> intro pointer bound
  · have createdIn := createdOps.inBounds_mono (.region pointer) bound
    have insertedIn := insertions.genericInBounds (.region pointer) createdIn
    have replacedIn := substitutions.genericInBounds (.region pointer) insertedIn
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (.region pointer) (by simp)).mpr replacedIn
  · have createdIn := createdOps.inBounds_mono (.block pointer) bound
    have insertedIn := insertions.genericInBounds (.block pointer) createdIn
    have replacedIn := substitutions.genericInBounds (.block pointer) insertedIn
    simpa [WfRewriter.eraseOp] using
      (Rewriter.eraseOp_inBounds (.block pointer) (by simp)).mpr replacedIn

/-- A preserved operation header preserves its function-interface view and body pointer. -/
theorem OperationHeaderPreserved.function_view {before after : IRContext OpCode} {op : OperationPtr}
    (header : OperationHeaderPreserved before after op) (source : FunctionOp before op) :
    ∃ target : FunctionOp after op, FunctionOp.of? op after = some target ∧
      target.getFunctionBody! = source.getFunctionBody! := by
  have present : (FunctionOp.of? op after).isSome = true := by
    have interfaceSome : (HasOpInfo.functionInterface? (op.getOpType! after)).isSome = true := by
      rw [header.opcode, source.functionInterface?_eq]
      rfl
    unfold FunctionOp.of?
    split <;> simp_all
  obtain ⟨target, found⟩ := Option.isSome_iff_exists.mp present
  exact ⟨target, found, header.region 0⟩

/-- The actual compiled driver retains the original function body, its region headers,
and its block argument interface. -/
theorem Pattern.fromLocalRewrite_function_body (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {function : OperationPtr} (functionIn : function.InBounds rewriter.ctx.raw)
    (source : FunctionOp rewriter.ctx.raw function)
    (hasBody : 0 < function.getNumRegions! rewriter.ctx.raw) :
    function.InBounds result.ctx.raw ∧
      ∃ target : FunctionOp result.ctx.raw function,
        FunctionOp.of? function result.ctx.raw = some target ∧
        target.getFunctionBody! = source.getFunctionBody! ∧
        source.getFunctionBody!.InBounds result.ctx.raw ∧
        source.getFunctionBody!.getParent! result.ctx.raw =
          source.getFunctionBody!.getParent! rewriter.ctx.raw ∧
        source.getFunctionBody!.getFirstBlock! result.ctx.raw =
          source.getFunctionBody!.getFirstBlock! rewriter.ctx.raw ∧
        RegionBlockHeadersPreserved rewriter.ctx.raw result.ctx.raw := by
  have different : function ≠ root := by intro same; subst function; omega
  have functionFinal := rule.fromLocalRewrite_existing_inBounds localRun run attached regions notOwn
    function functionIn different
  have header := (rule.fromLocalRewrite_existing_frame localRun run attached regions notOwn
    function functionIn different).1
  obtain ⟨target, found, bodySame⟩ := header.function_view source
  have headers := rule.fromLocalRewrite_regionBlockHeaders localRun run attached regions notOwn
  have regionBounds := (rule.fromLocalRewrite_region_block_inBounds localRun run attached regions notOwn).1
  have bodyIn := source.getFunctionBody!_inBounds rewriter.ctx.wellFormed.inBounds functionIn hasBody
  exact ⟨functionFinal, target, found, bodySame, regionBounds _ bodyIn,
    headers.regionParent _, headers.firstBlock _, headers⟩

end
end Veir.Puddle
