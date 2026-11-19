module
public import Veir.PatternRewriter.Puddle.CTreeModulePlacement
public import Veir.PatternRewriter.Puddle.CTreeGlobalSteps
public import Veir.Verifier
public import Veir.Verifier.FunctionControlFlow
public import Veir.PatternRewriter.Puddle.UnreachableDriverStructure
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeUnreachableRefinement
import all Veir.Interpreter.VariableState
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.GlobalOpInfo
import all Veir.Interfaces.FunctionInterfaces
public section
namespace Veir.Puddle.CTree

/-- Rewriting an unreachable root leaves every executable instruction unchanged.
The guarded driver supplies replacement safety independently of matcher dominance. -/
theorem Pattern.compile_moduleRefinement_of_unreachable
    (rule : Veir.Puddle.Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (unreachable : ¬ root.HierarchicallyReachable rewriter.ctx)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  cases matchRun : rule.matcher.run rewriter.ctx.raw root with
  | none => exact Pattern.compile_noMatch_moduleRefinement rule rootIn sourceVerified matchRun run
  | some matched =>
    have driverRun : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result := run
    cases localRun : rule.interpret rewriter.ctx root with
    | none => simp [RewritePattern.fromLocalRewrite, localRun] at driverRun
    | some localResult =>
      rcases localResult with ⟨created, replacement⟩
      cases replacement with
      | none =>
        simp only [Veir.Puddle.Pattern.interpret, matchRun] at localRun
        split at localRun <;> grind
      | some replacement =>
        rcases replacement with ⟨newOps, replacements⟩
        have notOwn := fromLocalRewrite_result_notOwn_indexed localRun driverRun
        have oldFields := rule.fromLocalRewrite_existing_frame localRun driverRun attached regions notOwn
        have frame := rule.fromLocalRewrite_unreachable_context_frame sourceVerified.dominance
          unreachable localRun driverRun attached regions
        have moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none := by
          simpa only [IRNode.parent!_operation, Option.map_eq_none_iff] using rootRooted.2
        intro function functionIn name named
        have different := named.ne_regionless sourceVerified functionIn regions
        obtain ⟨targetIn, targetNamed⟩ := rule.fromLocalRewrite_topLevelFunc localRun driverRun attached
          regions notOwn functionIn different named
        refine ⟨function, targetIn, targetNamed, ?_⟩
        cases sourceHeader : FunctionOp.of? function rewriter.ctx.raw with
        | none =>
          have functionLike : (HasOpInfo.functionInterface? (function.getOpType! rewriter.ctx.raw)).isSome := by
            rw [named.isFunc]
            rfl
          unfold FunctionOp.of? at sourceHeader
          split at sourceHeader <;> simp_all
        | some sourceFn =>
          have header := (oldFields function functionIn different).1
          obtain ⟨targetFn, targetHeader, bodySame⟩ := header.function_view sourceFn
          have headers : function.getNumRegions rewriter.ctx.raw = 1 →
              function.getNumRegions result.ctx.raw = 1 := by
            intro sourceOne
            have := header.numRegions
            simpa only [OperationPtr.getNumRegions!_eq_getNumRegions functionIn,
              OperationPtr.getNumRegions!_eq_getNumRegions targetIn, sourceOne] using this
          apply OperationPtr.isRefinedByAsFunctionCTree_of_bodies functionIn targetIn
            sourceFn targetFn sourceHeader targetHeader headers
          intro sourceValues targetValues mem values sourceOne
          have sourceBodyIn := sourceFn.getFunctionBody!_inBounds rewriter.ctx.wellFormed.inBounds
            functionIn (by simpa only [OperationPtr.getNumRegions!_eq_getNumRegions functionIn, sourceOne] using (by decide : 0 < 1))
          have targetBodyIn := targetFn.getFunctionBody!_inBounds result.ctx.wellFormed.inBounds
            targetIn (by simpa only [OperationPtr.getNumRegions!_eq_getNumRegions targetIn, headers sourceOne] using (by decide : 0 < 1))
          rw [bodySame] at targetBodyIn
          simp only [← FunctionOp.getFunctionBody!_eq_getFunctionBody, bodySame]
          suffices core : _root_.CTree.Sim (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2)
              (Veir.CTree.interpretCFGCore sourceFn.getFunctionBody! targetValues ⟨.empty result.ctx, mem⟩ targetBodyIn)
              (Veir.CTree.interpretCFGCore sourceFn.getFunctionBody! sourceValues ⟨.empty rewriter.ctx, mem⟩ sourceBodyIn) by
            apply _root_.CTree.Sim.trans
              (Veir.CTree.sim_interpretRegion_core _ targetValues ⟨.empty result.ctx, mem⟩ targetBodyIn).1
              (_root_.CTree.Sim.trans core
                (Veir.CTree.sim_interpretRegion_core _ sourceValues ⟨.empty rewriter.ctx, mem⟩ sourceBodyIn).2
                (fun t intermediate s related equal => by subst intermediate; exact related))
            intro t intermediate s equal related
            subst intermediate
            exact related
          have regionHeaders := rule.fromLocalRewrite_regionBlockHeaders localRun driverRun
            attached regions notOwn
          have firstSame := regionHeaders.firstBlock sourceFn.getFunctionBody!
          have firstSameChecked : sourceFn.getFunctionBody!.getFirstBlock result.ctx.raw targetBodyIn =
              sourceFn.getFunctionBody!.getFirstBlock rewriter.ctx.raw sourceBodyIn := by
            simpa only [← RegionPtr.getFirstBlock!_eq_getFirstBlock sourceBodyIn,
              ← RegionPtr.getFirstBlock!_eq_getFirstBlock targetBodyIn] using firstSame
          cases firstGet : sourceFn.getFunctionBody!.getFirstBlock! rewriter.ctx.raw with
          | none =>
            have sourceGet : sourceFn.getFunctionBody!.getFirstBlock rewriter.ctx.raw sourceBodyIn = none := by
              simpa only [← RegionPtr.getFirstBlock!_eq_getFirstBlock sourceBodyIn] using firstGet
            have targetGet := firstSameChecked.trans sourceGet
            rw [interpretCFGCore_eq_fail_of_no_firstBlock _ sourceBodyIn sourceGet]
            exact sim_fail _ _
          | some entry =>
            have sourceGet : sourceFn.getFunctionBody!.getFirstBlock rewriter.ctx.raw sourceBodyIn = some entry := by
              simpa only [← RegionPtr.getFirstBlock!_eq_getFirstBlock sourceBodyIn] using firstGet
            have targetGet := firstSameChecked.trans sourceGet
            have sourceEntryIn : entry.InBounds rewriter.ctx.raw := by grind
            have targetEntryIn : entry.InBounds result.ctx.raw := by grind
            have sourceHasBody : 0 < function.getNumRegions! rewriter.ctx.raw := by
              simpa only [OperationPtr.getNumRegions!_eq_getNumRegions functionIn, sourceOne] using (by decide : 0 < 1)
            have sourcePlacement := module_function_entry_placement sourceVerified moduleCode moduleNoParent
              functionIn named sourceFn sourceHasBody rfl firstGet
            have sourceBodyParent := sourceFn.getFunctionBody!_parent functionIn sourceHasBody
            have sourceBodyRooted : sourceFn.getFunctionBody!.RootedAt moduleOp rewriter.ctx :=
              sourcePlacement.1.of_parent (by
                simp only [IRNode.parent!_region, sourceBodyParent, Option.map_some])
            rw [interpretCFGCore_eq_of_firstBlock _ sourceBodyIn entry sourceEntryIn sourceGet,
              interpretCFGCore_eq_of_firstBlock _ targetBodyIn entry targetEntryIn targetGet]
            refine _root_.CTree.Sim.mono
              (RR := fun (t : InterpreterState result.ctx × Array RuntimeValue)
                (s : InterpreterState rewriter.ctx × Array RuntimeValue) =>
                Veir.CTree.PointerStateRefines s.1 t.1 ∧ RuntimeValue.arrayIsRefinedBy s.2 t.2)
              ?_ (fun _ _ related => related.2)
            apply Veir.CTree.sim_interpretCFGCore_reachable_frame
              Veir.OpCode.interpretCTree_monotone_assumed sourceVerified frame sourceFn.getFunctionBody!
            refine ⟨?_, ?_⟩
            · refine ⟨MemoryState.isRefinedBy_refl _, ?_⟩
              intro pointer value lookup
              simp [VariableState.empty, VariableState.getVar?] at lookup
            · exact ⟨rfl, values, by grind, sourcePlacement.2.1, sourcePlacement.2.2⟩

end Veir.Puddle.CTree
