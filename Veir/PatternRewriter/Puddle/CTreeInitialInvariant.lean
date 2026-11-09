module
public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.DriverFunctionStructure
public import Veir.PatternRewriter.Puddle.DriverScope
import all Veir.PatternRewriter.Puddle.DriverScope
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.MatcherIsolation
public import Veir.Interpreter.Refinement.CTree
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.IR.Basic
import all Veir.Rewriter.InsertPoint
import all Veir.Verifier
import all Veir.GlobalOpInfo
import all Veir.IR.OpInfo

import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.Datapath.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.Verif.OpInfo
import all Veir.Dialects.PDL.OpInfo
import all Veir.Dialects.IO.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.Test.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.LLZK.Include.OpInfo
import all Veir.Dialects.LLZK.Function.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.Seq.OpInfo
import all Veir.Dialects.Tensor.OpInfo
import all Veir.Dialects.SMT.OpInfo
namespace Veir.Puddle.CTree
public section

private theorem function_requires_terminator {ctx : IRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx op) (index : Nat) :
    HasOpInfo.hasNoTerminator (op.getOpType! ctx) index = false := by
  have present : (HasOpInfo.functionInterface? (op.getOpType! ctx)).isSome = true := by
    rw [function.functionInterface?_eq]; rfl
  generalize codeEq : op.getOpType! ctx = code at present ⊢
  cases code <;> rename_i dialectCode <;> cases dialectCode
  all_goals first | rfl | change false = true at present; contradiction

/-- Verified function-body entry blocks contain an operation. -/
theorem verified_function_entry_nonempty {ctx : WfIRContext OpCode} {verifyRoot owner : OperationPtr}
    (verified : ctx.Verified verifyRoot) (function : FunctionOp ctx.raw owner)
    {region : RegionPtr} {entry : BlockPtr} (entryIn : entry.InBounds ctx.raw)
    (blockParent : entry.getParent! ctx.raw = some region)
    (regionParent : region.getParent! ctx.raw = some owner) :
    ∃ first, entry.getFirstOp! ctx.raw = some first := by
  have checked := verified
  simp only [WfIRContext.Verified, WfIRContext.verify] at checked
  split at checked
  · cases checked
  split at checked
  · cases checked
  obtain ⟨_, _, rest⟩ := Except.bind_eq_ok.mp checked
  obtain ⟨_, blocks, _⟩ := Except.bind_eq_ok.mp rest
  have blockCheck := IRContext.forBlocksDepM_except_ok blocks entry entryIn
  obtain ⟨_, terminator, _⟩ := Except.bind_eq_ok.mp blockCheck
  have required : region.hasNoTerminator ctx = false := by
    simp [RegionPtr.hasNoTerminator, regionParent, function_requires_terminator function]
  have noEscape : entry.mayBeValidWithoutTerminator ctx entryIn = false := by
    simp [BlockPtr.mayBeValidWithoutTerminator, ← BlockPtr.getParent!_eq_getParent entryIn,
      blockParent, regionParent, required]
  unfold BlockPtr.verifyTerminator at terminator
  rw [noEscape] at terminator
  simp only [Bool.false_eq_true, ↓reduceIte] at terminator
  cases lastGet : entry.getLastOp! ctx.raw with
  | none =>
      have lastNone : entry.getLastOp ctx.raw entryIn = none := by grind
      simp [lastNone] at terminator
  | some last =>
      obtain ⟨ops, chain⟩ := ctx.wellFormed.opChain entry entryIn
      cases firstGet : entry.getFirstOp! ctx.raw with
      | none =>
          have := chain.firstOp_eq_none_iff_lastOp_eq_none
          grind
      | some first => exact ⟨first, rfl⟩

/-- Installing related entry arguments in two initially empty contexts produces related
variable states whenever the block's argument interface and mapping are preserved. -/
theorem empty_entry_setters_refine
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {entry : BlockPtr} (sourceIn : entry.InBounds sourceCtx.raw) (targetIn : entry.InBounds targetCtx.raw)
    (argumentTypes : entry.getArgumentTypes! targetCtx.raw = entry.getArgumentTypes! sourceCtx.raw)
    (mappingArgs : ∀ (index : Nat) (bounds : (entry.getArgument index : ValuePtr).InBounds sourceCtx.raw),
      (mapping ⟨entry.getArgument index, bounds⟩).val = entry.getArgument index)
    {sourceArgs targetArgs : Array RuntimeValue} (args : RuntimeValue.arrayIsRefinedBy sourceArgs targetArgs)
    {sourceVars : VariableState sourceCtx}
    (sourceSet : (VariableState.empty sourceCtx).setArgumentValues? entry sourceArgs sourceIn = some sourceVars) :
    ∃ targetVars, (VariableState.empty targetCtx).setArgumentValues? entry targetArgs targetIn = some targetVars ∧
      sourceVars.isRefinedBy targetVars mapping := by
  have count : entry.getNumArguments! targetCtx.raw = entry.getNumArguments! sourceCtx.raw := by
    have size := congrArg Array.size argumentTypes
    simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using size
  have sourceSize : sourceArgs.size = entry.getNumArguments! sourceCtx.raw := by
    unfold VariableState.setArgumentValues? at sourceSet
    split at sourceSet <;> simp_all
  have targetSize : targetArgs.size = entry.getNumArguments! targetCtx.raw := by
    have size := args.1
    omega
  have sourceConforms :=
    (VariableState.setArgumentValues?_isSome_iff_conforms (VariableState.empty sourceCtx) sourceSize).mpr
      ⟨sourceVars, sourceSet⟩
  have typeEq (index : Nat) (bound : index < entry.getNumArguments! sourceCtx.raw) :
      (entry.getArgument index : ValuePtr).getType! targetCtx.raw =
        (entry.getArgument index : ValuePtr).getType! sourceCtx.raw := by
    have sizeSource : index < (entry.getArgumentTypes! sourceCtx.raw).size := by grind
    have sizeTarget : index < (entry.getArgumentTypes! targetCtx.raw).size := by grind
    have same := congrArg (fun types : Array TypeAttr => types[index]!) argumentTypes
    simpa only [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument (by omega : index < entry.getNumArguments! targetCtx.raw),
      BlockPtr.getArgumentTypes!.getElem!_eq_getArgument bound, ValuePtr.getType!] using same
  obtain ⟨targetVars, targetSet⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms (VariableState.empty targetCtx) targetSize).mp (by
      intro i hi
      rw [typeEq i (by omega)]
      exact (sourceConforms i (by omega)).of_isRefinedBy (args.2 i (by omega)))
  refine ⟨targetVars, targetSet, ?_⟩
  intro pointer pointerIn sourceValue sourceGet
  have sourceLookup := VariableState.getVar?_setArgumentValues? sourceSet (value := pointer)
  rw [sourceLookup] at sourceGet
  cases pointer with
  | opResult => simp [VariableState.empty, VariableState.getVar?] at sourceGet
  | blockArgument argument =>
    rcases argument with ⟨owner, index⟩
    simp only at sourceGet
    split at sourceGet
    · rename_i bound
      obtain ⟨same, indexIn⟩ := bound
      subst owner
      cases sourceGet
      have pointerEq : (ValuePtr.blockArgument ⟨entry, index⟩) = entry.getArgument index := rfl
      have mapped := mappingArgs index (by simpa only [← pointerEq] using pointerIn)
      refine ⟨targetArgs[index]!, ?_, args.2 index (by omega)⟩
      rw [show (mapping ⟨ValuePtr.blockArgument ⟨entry, index⟩, pointerIn⟩).val = entry.getArgument index by exact mapped]
      exact VariableState.getVar?_getArgument_of_setArgumentValues? (by omega) targetSet
    · simp [VariableState.empty, VariableState.getVar?] at sourceGet

/-- Entry argument installation in the target realizes every source entry slot, with the
original source type. This statement is independent of the target's context type. -/
theorem empty_entry_lookup_target {sourceCtx targetCtx : WfIRContext OpCode}
    {entry : BlockPtr} {sourceIn : entry.InBounds sourceCtx.raw} {targetIn : entry.InBounds targetCtx.raw}
    (argumentTypes : entry.getArgumentTypes! targetCtx.raw = entry.getArgumentTypes! sourceCtx.raw)
    {sourceArgs targetArgs : Array RuntimeValue} {sourceVars : VariableState sourceCtx} {targetVars : VariableState targetCtx}
    (sourceSet : (VariableState.empty sourceCtx).setArgumentValues? entry sourceArgs sourceIn = some sourceVars)
    (targetSet : (VariableState.empty targetCtx).setArgumentValues? entry targetArgs targetIn = some targetVars)
    (pointer : ValuePtr) (available : (sourceVars.getVar? pointer).isSome = true) :
    ∃ value, targetVars.getVar? pointer = some value ∧ value.Conforms (pointer.getType! sourceCtx.raw) := by
  have lookup := VariableState.getVar?_setArgumentValues? sourceSet (value := pointer)
  rw [lookup] at available
  have count : entry.getNumArguments! targetCtx.raw = entry.getNumArguments! sourceCtx.raw := by
    have size := congrArg Array.size argumentTypes
    simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using size
  cases pointer with
  | opResult => simp [VariableState.empty, VariableState.getVar?] at available
  | blockArgument argument =>
    rcases argument with ⟨owner, index⟩
    simp only at available
    split at available
    · rename_i bound
      obtain ⟨same, indexIn⟩ := bound
      subst owner
      have targetGet := VariableState.getVar?_getArgument_of_setArgumentValues? (by omega : index < entry.getNumArguments! targetCtx.raw) targetSet
      have typed := VariableState.getVar?_conforms targetGet
      have sameType := congrArg (fun types : Array TypeAttr => types[index]!) argumentTypes
      rw [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument (by omega),
        BlockPtr.getArgumentTypes!.getElem!_eq_getArgument indexIn] at sameType
      refine ⟨_, targetGet, ?_⟩
      change targetArgs[index]!.Conforms ((entry.getArgument index).getType! targetCtx.raw) at typed
      rw [sameType] at typed
      simpa only [ValuePtr.getType!, BlockPtr.getArgument] using typed
    · simp [VariableState.empty, VariableState.getVar?] at available

/-- Related arguments and concrete entry alignment establish the actual CFG block invariant.
The entry-state fields are proved here; the alignment premise contains only structural IR facts. -/
theorem initial_rewriteCFGInvariant_block
    {sourceCtx targetCtx : WfIRContext OpCode} (mapping : ValueMapping sourceCtx targetCtx)
    (rewriteRoot : OperationPtr) (newOps : Array OperationPtr)
    {sourceRegion targetRegion : RegionPtr} {entry : BlockPtr}
    (sourceIn : entry.InBounds sourceCtx.raw) (targetIn : entry.InBounds targetCtx.raw)
    (sourceFirstBlock : sourceRegion.getFirstBlock! sourceCtx.raw = some entry)
    (targetFirstBlock : targetRegion.getFirstBlock! targetCtx.raw = some entry)
    (sourceParent : entry.getParent! sourceCtx.raw = some sourceRegion)
    (targetParent : entry.getParent! targetCtx.raw = some targetRegion)
    (sourceSSA : sourceRegion.hasSSADominance sourceCtx)
    (targetSSA : targetRegion.hasSSADominance targetCtx)
    (sourceRooted : entry.RootedAt sourceIrRoot sourceCtx)
    (targetRooted : entry.RootedAt targetIrRoot targetCtx)
    (argumentTypes : entry.getArgumentTypes! targetCtx.raw = entry.getArgumentTypes! sourceCtx.raw)
    (mappingArgs : ∀ (index : Nat) (bounds : (entry.getArgument index : ValuePtr).InBounds sourceCtx.raw),
      (mapping ⟨entry.getArgument index, bounds⟩).val = entry.getArgument index)
    (alignment : ∀ first (_firstIn : first.InBounds sourceCtx.raw), entry.getFirstOp! sourceCtx.raw = some first →
      ∃ targetFirst, targetFirst.InBounds targetCtx.raw ∧ entry.getFirstOp! targetCtx.raw = some targetFirst ∧
        redirectedOperation sourceCtx.raw rewriteRoot newOps first = some targetFirst ∧
        first.HierarchicallyReachable sourceCtx ∧ targetFirst.HierarchicallyReachable targetCtx)
    (mem : MemoryState)
    {sourceArgs targetArgs : Array RuntimeValue} (args : RuntimeValue.arrayIsRefinedBy sourceArgs targetArgs) :
    RewriteCFGInvariant mapping rewriteRoot newOps sourceRegion targetRegion
      (.inl (⟨entry, targetIn⟩, targetArgs), ⟨.empty targetCtx, mem⟩)
      (.inl (⟨entry, sourceIn⟩, sourceArgs), ⟨.empty sourceCtx, mem⟩) := by
  refine RewriteCFGInvariant.block (sourceBlock := ⟨entry, sourceIn⟩)
    (targetBlock := ⟨entry, targetIn⟩) rfl ?_
  intro sourceVars sourceSet first firstIn firstGet
  obtain ⟨targetVars, targetSet, related⟩ := empty_entry_setters_refine sourceIn targetIn
    argumentTypes mappingArgs args sourceSet
  obtain ⟨targetFirst, targetFirstIn, targetFirstGet, aligned, sourceReachable, targetReachable⟩ :=
    alignment first firstIn firstGet
  refine ⟨targetVars, targetFirst, targetFirstIn, targetSet, targetFirstGet, ?_⟩
  have sourceStart : InsertPoint.atStart! entry sourceCtx.raw = .before first := by
    simp [InsertPoint.atStart!_eq, firstGet]
  have targetStart : InsertPoint.atStart! entry targetCtx.raw = .before targetFirst := by
    simp [InsertPoint.atStart!_eq, targetFirstGet]
  have sourceDefined := InterpreterState.definesDominatingIn_entry mem
    sourceFirstBlock sourceParent sourceSSA sourceRooted sourceSet
  have targetDefined := InterpreterState.definesDominatingIn_entry mem
    targetFirstBlock targetParent targetSSA targetRooted targetSet
  rw [sourceStart] at sourceDefined
  rw [targetStart] at targetDefined
  refine ⟨aligned, ?_, ?_, sourceReachable, targetReachable, ?_, sourceDefined, targetDefined, ?_, ?_, ?_⟩
  · grind
  · grind
  · refine ⟨MemoryState.isRefinedBy_refl _, ?_⟩
    intro pointer bounds sourceScope targetScope sourceValue sourceGet targetValue targetGet
    obtain ⟨value, get, refining⟩ := related pointer bounds sourceValue sourceGet
    rw [targetGet] at get
    cases get
    exact refining
  · intro pointer bounds inside static dynamic sourceValue targetValue sourceGet targetGet
    have lookup := VariableState.getVar?_setArgumentValues? sourceSet (value := pointer)
    have sourceOriginal := sourceGet
    rw [lookup] at sourceGet
    cases pointer with
    | opResult => simp [VariableState.empty, VariableState.getVar?] at sourceGet
    | blockArgument argument =>
      rcases argument with ⟨owner, index⟩
      simp only at sourceGet
      split at sourceGet
      · rename_i bound
        obtain ⟨same, indexIn⟩ := bound
        subst owner
        have mapped := mappingArgs index (by simpa only [BlockPtr.getArgument] using bounds)
        obtain ⟨value, get, refining⟩ := related _ bounds sourceValue sourceOriginal
        rw [show (mapping ⟨ValuePtr.blockArgument ⟨entry, index⟩, bounds⟩).val =
          ValuePtr.blockArgument ⟨entry, index⟩ by simpa only [BlockPtr.getArgument] using mapped] at get
        rw [targetGet] at get
        cases get
        exact refining
      · simp [VariableState.empty, VariableState.getVar?] at sourceGet
  · intro pointer bounds inside static dynamic
    have available := sourceDefined pointer bounds inside dynamic
    exact empty_entry_lookup_target argumentTypes sourceSet targetSet pointer available
  · have history := ValueResolver.ctreeEquationLemmaIn_entry targetVars.getVar? rewriteRoot
      sourceFirstBlock sourceParent sourceSSA sourceRooted
    simpa only [sourceStart] using history

/-- Actual driver/header facts discharge entry alignment, mapping, and argument-interface
premises of the initial invariant. Entry reachability/rootedness are module placement facts. -/
theorem Pattern.fromLocalRewrite_initial_invariant (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {function verifyRoot : OperationPtr} (functionIn : function.InBounds rewriter.ctx.raw)
    (sourceFunction : FunctionOp rewriter.ctx.raw function)
    (hasBody : 0 < function.getNumRegions! rewriter.ctx.raw)
    (outputVerified : result.ctx.Verified verifyRoot)
    {region : RegionPtr} (body : sourceFunction.getFunctionBody! = region)
    {entry : BlockPtr} (entryIn : entry.InBounds rewriter.ctx.raw)
    (firstBlock : region.getFirstBlock! rewriter.ctx.raw = some entry)
    (sourceRooted : entry.RootedAt sourceIrRoot rewriter.ctx)
    (targetRooted : entry.RootedAt targetIrRoot result.ctx)
    (sourceReachable : entry.HierarchicallyReachable rewriter.ctx)
    (targetReachable : entry.HierarchicallyReachable result.ctx)
    (mem : MemoryState)
    {sourceArgs targetArgs : Array RuntimeValue} (args : RuntimeValue.arrayIsRefinedBy sourceArgs targetArgs) :
    RewriteCFGInvariant (rule.fromLocalRewrite_mapping localRun run attached regions notOwn)
      root newOps region region
      (.inl (⟨entry, (rule.fromLocalRewrite_region_block_inBounds localRun run attached regions notOwn).2 entry entryIn⟩,
        targetArgs), ⟨.empty result.ctx, mem⟩)
      (.inl (⟨entry, entryIn⟩, sourceArgs), ⟨.empty rewriter.ctx, mem⟩) := by
  obtain ⟨functionFinal, targetFunction, targetView, bodySame, bodyFinal, regionParentSame, firstBlockSame, headers⟩ :=
    rule.fromLocalRewrite_function_body localRun run attached regions notOwn functionIn sourceFunction hasBody
  have functionDifferent : function ≠ root := by intro same; subst function; omega
  have functionHeader := (rule.fromLocalRewrite_existing_frame localRun run attached regions notOwn
    function functionIn functionDifferent).1
  have targetHasBody : 0 < function.getNumRegions! result.ctx.raw := by
    rw [functionHeader.numRegions]; exact hasBody
  have entryFinal := (rule.fromLocalRewrite_region_block_inBounds localRun run attached regions notOwn).2 entry entryIn
  have sourceParent : entry.getParent! rewriter.ctx.raw = some region := by grind
  have targetParent : entry.getParent! result.ctx.raw = some region := (headers.blockParent entry).trans sourceParent
  have targetFirstBlock : region.getFirstBlock! result.ctx.raw = some entry := (headers.firstBlock region).trans firstBlock
  have sourceSSA : region.hasSSADominance rewriter.ctx := by
    simpa only [body] using (sourceFunction.body_scope functionIn hasBody).2
  have targetSSA : region.hasSSADominance result.ctx := by
    simpa only [bodySame, body] using (targetFunction.body_scope functionFinal targetHasBody).2
  have targetRegionParent : region.getParent! result.ctx.raw = some function := by
    simpa only [bodySame, body] using targetFunction.getFunctionBody!_parent functionFinal targetHasBody
  obtain ⟨targetFirst, targetFirstGet⟩ := verified_function_entry_nonempty outputVerified targetFunction
    entryFinal targetParent targetRegionParent
  apply initial_rewriteCFGInvariant_block _ root newOps entryIn entryFinal firstBlock targetFirstBlock
    sourceParent targetParent sourceSSA targetSSA sourceRooted targetRooted (headers.argumentTypes entry) ?_ ?_ mem args
  · intro index bound
    unfold Pattern.fromLocalRewrite_mapping
    apply rootValueMapping_of_notResult
    intro member
    obtain ⟨i, _, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    simp [OperationPtr.getResult, BlockPtr.getArgument] at equal
  · intro first firstIn firstGet
    have targetFirstIn : targetFirst.InBounds result.ctx.raw := by grind
    refine ⟨targetFirst, targetFirstIn, targetFirstGet, ?_, ?_, ?_⟩
    · by_cases same : first = root
      · subst first
        have entryEq := rule.fromLocalRewrite_block_entry localRun run attached regions notOwn _ entryIn firstGet
        have redir : redirectedOperation rewriter.ctx.raw root newOps root = entry.getFirstOp! result.ctx.raw := by
          rw [entryEq]
          unfold redirectedOperation
          simp only [↓reduceIte]
          rw [← Array.getElem?_toList]
          cases newOps.toList <;> rfl
        exact redir.trans targetFirstGet
      · have unchanged := rule.fromLocalRewrite_other_block_entry localRun run attached regions notOwn
          entry entryIn (by grind)
        have equal : targetFirst = first := by grind
        simp [redirectedOperation, same, equal]
    · exact OperationPtr.HierarchicallyReachable.of_parent_block sourceReachable (by grind)
    · exact OperationPtr.HierarchicallyReachable.of_parent_block targetReachable (by grind)

end
end Veir.Puddle.CTree
