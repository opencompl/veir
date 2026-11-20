module

public import Veir.PatternRewriter.Puddle.CTreeSurvivingCFG
public import Veir.PatternRewriter.Puddle.CTreeVerificationPreservation
public import Veir.PatternRewriter.Puddle.CTreeInitialInvariant
public import Veir.PatternRewriter.Puddle.CTreeModulePlacement
public import Veir.PatternRewriter.Puddle.CTreeUnreachableSoundness
public import Veir.Verifier.FunctionControlFlow
public import Veir.PatternRewriter.Puddle.CTreeRootStep
public import Veir.PatternRewriter.Puddle.DriverFunctionStructure
public import Veir.Interpreter.CTreeSimulation
public import Veir.PatternRewriter.Puddle.CTreeGlobalSteps
public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.MatcherResolverHistory
public import Veir.PatternRewriter.Puddle.MatcherIsolation
public import Veir.Verifier
public import Veir.Interpreter.CTreeFunctionRefinement
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.Interfaces.FunctionInterfaces
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.PatternRewriter.Puddle.CreationCheckedSemantics
import all Veir.PatternRewriter.Puddle.DriverScope
import all Veir.IR.OpCode
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo

public section
namespace Veir.Puddle.CTree

/-- End-to-end contextual compiler soundness. The root lies in an SSA region;
verification of the produced IR is the explicit compiler-output obligation. -/
theorem Pattern.Valid.compile_moduleRefinement_of_verified_output_of_reachable
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (targetVerified : result.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  have sourceDom : rewriter.ctx.Dom moduleOp := sourceVerified.dominance
  have targetDom : result.ctx.Dom moduleOp := targetVerified.dominance
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
        have contract := valid.replacement_contract_of_interpret sourceDom rootRooted rootRegion rootSSA
          rootReachable rootIn localRun
        let mapping := rule.fromLocalRewrite_mapping localRun driverRun attached regions contract.1
        obtain ⟨resultMapping, mappingEq, otherResults⟩ :=
          rule.fromLocalRewrite_mapping_properties localRun driverRun attached regions contract.1
        have fixedOther : ∀ value (valueIn : value.InBounds rewriter.ctx.raw),
            value ∉ root.getResults! rewriter.ctx.raw → (mapping ⟨value, valueIn⟩).val = value := by
          intro value valueIn notResult
          dsimp only [mapping]
          unfold Veir.Puddle.Pattern.fromLocalRewrite_mapping
          exact rootValueMapping_of_notResult root replacements _ _ _ valueIn notResult
        obtain ⟨oldFields, insertedChain, insertedParents⟩ :=
          valid.fromLocalRewrite_frame_and_splice sourceDom rootRooted rootRegion rootSSA rootReachable
            localRun driverRun attached regions
        have moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none := by
          simpa only [IRNode.parent!_operation, Option.map_eq_none_iff] using rootRooted.2
        have moduleIn : moduleOp.InBounds rewriter.ctx.raw := by
          by_cases inside : moduleOp.InBounds rewriter.ctx.raw
          · exact inside
          · simp only [OperationPtr.getOpType!, OperationPtr.get!_of_not_inBounds inside] at moduleCode
            contradiction
        have moduleDifferent : moduleOp ≠ root := by
          intro equal
          subst root
          simp [moduleNoParent] at attached
        have moduleHeader := (oldFields moduleOp moduleIn moduleDifferent).1
        have targetModuleCode := moduleHeader.opcode.trans moduleCode
        have targetModuleNoParent := moduleHeader.parent.trans moduleNoParent
        intro function functionIn name named
        have different := named.ne_regionless sourceVerified functionIn regions
        obtain ⟨targetIn, targetNamed⟩ := rule.fromLocalRewrite_topLevelFunc localRun driverRun attached
          regions contract.1 functionIn different named
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
            attached regions contract.1
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
            have targetHasBody : 0 < function.getNumRegions! result.ctx.raw := by
              rw [header.numRegions]
              exact sourceHasBody
            have sourcePlacement := module_function_entry_placement sourceVerified moduleCode moduleNoParent
              functionIn named sourceFn sourceHasBody rfl firstGet
            have targetFirstBlock : targetFn.getFunctionBody!.getFirstBlock! result.ctx.raw = some entry := by
              rw [bodySame]
              exact firstSame.trans firstGet
            have targetPlacement := module_function_entry_placement targetVerified targetModuleCode targetModuleNoParent
              targetIn targetNamed targetFn targetHasBody bodySame (firstSame.trans firstGet)
            have sourceBodyParent := sourceFn.getFunctionBody!_parent functionIn sourceHasBody
            have targetBodyParent : sourceFn.getFunctionBody!.getParent! result.ctx.raw = some function := by
              simpa only [bodySame] using targetFn.getFunctionBody!_parent targetIn targetHasBody
            have sourceBodyRooted : sourceFn.getFunctionBody!.RootedAt moduleOp rewriter.ctx :=
              sourcePlacement.1.of_parent (by
                simp only [IRNode.parent!_region, sourceBodyParent, Option.map_some])
            have targetBodyRooted : sourceFn.getFunctionBody!.RootedAt moduleOp result.ctx :=
              targetPlacement.1.of_parent (by
                simp only [IRNode.parent!_region, targetBodyParent, Option.map_some])
            have bodySSA := (sourceFn.body_scope functionIn sourceHasBody).2
            rw [interpretCFGCore_eq_of_firstBlock _ sourceBodyIn entry sourceEntryIn sourceGet,
              interpretCFGCore_eq_of_firstBlock _ targetBodyIn entry targetEntryIn targetGet]
            refine _root_.CTree.Sim.iter_batched
              (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
              (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
              (rewriteTargetBatch newOps) (rewriteSourceBatch root newOps)
              (rewriteTargetBatch_positive newOps) (rewriteSourceBatch_positive root newOps)
              (RewriteCFGInvariant mapping root newOps sourceFn.getFunctionBody! sourceFn.getFunctionBody!)
              (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2) ?step ?initial
            case step =>
              intro target source invariant
              cases invariant with
              | block sameBlock pending =>
                simpa only [rewriteTargetBatch, rewriteSourceBatch, _root_.CTree.iterSteps_one] using
                  rewriteCFGInvariant_block_step pending (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2)
              | @operation sourceOp targetOp sourceState targetState operationInvariant =>
                by_cases isRoot : sourceOp.val = root
                · rcases sourceOp with ⟨sourceOp, sourceOpIn⟩
                  dsimp only at isRoot
                  subst sourceOp
                  have currentRegion : region = sourceFn.getFunctionBody! := by
                    exact Option.some.inj (rootRegion.symm.trans operationInvariant.sourceParent)
                  obtain ⟨block, rootParent, blockParent⟩ :=
                    OperationPtr.getParentRegion!_eq_some_iff.mp rootRegion
                  have blockIn : block.InBounds rewriter.ctx.raw := by grind
                  have bodyParent : sourceFn.getFunctionBody!.getParent! rewriter.ctx.raw = some function :=
                    sourceFn.getFunctionBody!_parent functionIn (by
                      simpa only [OperationPtr.getNumRegions!_eq_getNumRegions functionIn, sourceOne] using (by decide : 0 < 1))
                  have regionParent : region.getParent! rewriter.ctx.raw = some function := by
                    simpa only [currentRegion] using bodyParent
                  have rootNonterm := valid.root_nonterminator_of_interpret localRun
                  obtain ⟨next, nextEq⟩ := sourceVerified.nonterminator_hasNext_in_func blockIn named.isFunc
                    regionParent blockParent rootParent rootNonterm
                  have nextDifferent : next ≠ root := by
                    intro equal
                    subst next
                    exact root_ne_own_predecessor rootIn attached
                      (IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some rootIn
                        rewriter.ctx.wellFormed nextEq)
                  have nextIn : next.InBounds rewriter.ctx.raw := by grind
                  have targetNextIn := rule.fromLocalRewrite_existing_inBounds localRun driverRun attached
                    regions contract.1 next nextIn nextDifferent
                  have nextParent : next.getParent! rewriter.ctx.raw = some block := by grind
                  have nextTargetParent := (oldFields next nextIn nextDifferent).1.parent.trans nextParent
                  have targetBlockParent := (regionHeaders.blockParent block).trans blockParent
                  have sourceScope : region.nearestIsolatedScope? rewriter.ctx.raw = some region := by
                    simpa only [← currentRegion] using (sourceFn.body_scope functionIn (by
                      simpa only [OperationPtr.getNumRegions!_eq_getNumRegions functionIn, sourceOne] using (by decide : 0 < 1))).1
                  have starts : (newOps.toList.head? <|> some next) = some targetOp.val := by
                    have aligned := operationInvariant.aligned
                    have headEq : newOps.toList.head? = newOps[0]? := by
                      rw [← Array.getElem?_toList]
                      cases newOps.toList <;> rfl
                    rw [headEq]
                    simpa only [redirectedOperation, ↓reduceIte, nextEq] using aligned
                  have checked := valid.root_checked_invariant sourceVerified targetVerified rootRooted rootRegion
                    rootSSA rootReachable sourceScope localRun driverRun attached regions resultMapping.symm fixedOther
                    targetOp.val next targetOp.property nextIn targetNextIn starts nextEq nextDifferent rootParent
                    blockParent targetBlockParent nextParent nextTargetParent sourceState targetState
                    (by simpa only [currentRegion] using operationInvariant)
                  cases listEq : newOps.toList with
                  | nil =>
                    have emptyArray : newOps = #[] := Array.toList_inj.mp listEq
                    have targetEqual : targetOp.val = next := by simpa [listEq] using starts.symm
                    have targetPointer : targetOp = ⟨next, targetNextIn⟩ := Subtype.ext targetEqual
                    subst targetOp
                    have targetBatch : rewriteTargetBatch newOps (.inr ⟨next, targetNextIn⟩, targetState) = 1 := by
                      simp only [emptyArray, rewriteTargetBatch]
                      rfl
                    have sourceBatch : rewriteSourceBatch root newOps (.inr ⟨root, sourceOpIn⟩, sourceState) = 2 := by
                      simp only [emptyArray, rewriteSourceBatch]
                      rfl
                    rw [targetBatch, sourceBatch, _root_.CTree.iterSteps_one]
                    have deleted : _root_.CTree.Sim (fun target source =>
                        RewriteOpInvariant mapping root newOps sourceFn.getFunctionBody! sourceFn.getFunctionBody!
                          ⟨next, nextIn⟩ ⟨next, targetNextIn⟩ source.1 target)
                        (pure targetState : Tree (InterpreterState result.ctx))
                        (Veir.CTree.interpretOpCore root sourceState rootIn) := by
                      simpa only [listEq, interpretCreatedOpsChecked, currentRegion] using
                        checked.mono (fun _ _ h => h.1)
                    apply sim_cfgDeletedRoot root next rootIn nextIn nextEq rootNonterm sourceState targetState
                      (fun state => Veir.CTree.interpretCFGCore.iter (.inr ⟨next, targetNextIn⟩) state)
                      (Sum.LiftRel (RewriteCFGInvariant mapping root newOps sourceFn.getFunctionBody! sourceFn.getFunctionBody!)
                        (fun target source => RuntimeValue.arrayIsRefinedBy source.2 target.2))
                      (fun target source => RewriteOpInvariant mapping root newOps sourceFn.getFunctionBody! sourceFn.getFunctionBody!
                        ⟨next, nextIn⟩ ⟨next, targetNextIn⟩ source target) deleted
                    intro target source nextInvariant
                    exact valid.surviving_CFG sourceVerified targetVerified rootRooted rootRegion rootSSA rootReachable
                      localRun driverRun attached regions contract.1 rfl mappingEq otherResults named.isFunc
                      sourceBodyParent targetBodyParent targetFn sourceBodyRooted targetBodyRooted bodySSA
                      nextIn targetNextIn nextDifferent nextInvariant
                  | cons head tail =>
                    have headGet : newOps.toList.head? = some targetOp.val := by simpa [listEq] using starts
                    have arrayHead : newOps[0]? = some targetOp.val := by
                      rw [← Array.getElem?_toList]
                      simpa [listEq] using headGet
                    have positive : 0 < newOps.size := by
                      have sizeEq := congrArg List.length listEq
                      simp only [Array.length_toList, List.length_cons] at sizeEq
                      omega
                    rw [rewriteTargetBatch_at_head newOps targetOp targetState arrayHead positive,
                      rewriteSourceBatch_nonempty root newOps _ positive, _root_.CTree.iterSteps_one]
                    have createdBounds : ∀ op ∈ newOps.toList, op.InBounds result.ctx.raw := by
                      intro op member
                      exact (valid.fromLocalRewrite_created_fields sourceDom rootRooted rootRegion rootSSA
                        rootReachable localRun driverRun attached regions op (by simpa using member)).1
                    have createdNonterm : ∀ op ∈ newOps.toList, (op.getOpType! result.ctx.raw).isTerminator = false := by
                      intro op member
                      exact valid.fromLocalRewrite_created_nonterminator sourceDom rootRooted rootRegion rootSSA
                        rootReachable localRun driverRun attached regions op (by simpa using member)
                    have cfg := sim_cfgBatch_of_checkedRoot newOps.toList targetOp.val next root next
                      targetOp.property targetNextIn rootIn nextIn headGet createdBounds
                      (by simpa only [nextEq] using insertedChain) createdNonterm rootNonterm nextEq
                      sourceState targetState
                      (fun target source => RewriteOpInvariant mapping root newOps region region
                        ⟨next, nextIn⟩ ⟨next, targetNextIn⟩ source target)
                      (checked.mono (fun _ _ h => h.1))
                      (reachable := RewriteCFGInvariant mapping root newOps region region)
                      (fun target source related => .operation related)
                    have widened := cfg.mono
                      (RS := Sum.LiftRel (RewriteCFGInvariant mapping root newOps region region)
                        (fun target source => RuntimeValue.arrayIsRefinedBy source.2 target.2)) (by
                      intro target source related
                      cases related with
                      | inl h => exact Sum.LiftRel.inl h
                      | inr impossible => exact False.elim impossible)
                    simpa only [Array.length_toList, currentRegion] using widened
                · have aligned := operationInvariant.aligned
                  have sameOp : targetOp.val = sourceOp.val := by
                    simpa only [redirectedOperation, ite_eq_right isRoot, Option.some.injEq] using aligned.symm
                  have targetCurrentIn : sourceOp.val.InBounds result.ctx.raw := by
                    simpa only [sameOp] using targetOp.property
                  have targetEqual : targetOp = ⟨sourceOp.val, targetCurrentIn⟩ := Subtype.ext sameOp
                  subst targetOp
                  obtain ⟨sourceCount, targetCount⟩ := Pattern.surviving_batch_counts rule localRun sourceOp.property
                    targetCurrentIn isRoot sourceState targetState
                  rw [sourceCount, targetCount, _root_.CTree.iterSteps_one, _root_.CTree.iterSteps_one]
                  exact valid.surviving_CFG sourceVerified targetVerified rootRooted rootRegion rootSSA rootReachable
                    localRun driverRun attached regions contract.1 rfl mappingEq otherResults named.isFunc
                    sourceBodyParent targetBodyParent targetFn sourceBodyRooted targetBodyRooted bodySSA
                    sourceOp.property targetCurrentIn isRoot operationInvariant
            case initial =>
              exact Pattern.fromLocalRewrite_initial_invariant rule localRun driverRun attached regions contract.1
                functionIn sourceFn sourceHasBody targetVerified rfl sourceEntryIn firstGet
                sourcePlacement.2.1 targetPlacement.2.1 sourcePlacement.2.2 targetPlacement.2.2 mem values
/-- A valid pattern's successful compilation refines its original verified module.
Output verification is supplied by the separately stated preservation axiom. -/
theorem Pattern.Valid.compile_moduleRefinement_of_reachable
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr} {region : RegionPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp rootRegion
  have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
  have targetVerified := valid.compile_preservesVerified rootIn moduleCode sourceVerified rootRooted
    rootRegion rootSSA attached regions run
  exact valid.compile_moduleRefinement_of_verified_output_of_reachable rootIn moduleCode sourceVerified targetVerified
    rootRooted rootRegion rootSSA rootReachable attached regions run

/-- End-to-end soundness for reachable and unreachable roots. Output verification is
an explicit obligation only used by the reachable-root branch. -/
theorem Pattern.Valid.compile_moduleRefinement_of_verified_output
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (targetVerified : result.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  classical
  by_cases reachable : root.HierarchicallyReachable rewriter.ctx
  · exact valid.compile_moduleRefinement_of_verified_output_of_reachable rootIn moduleCode
      sourceVerified targetVerified rootRooted rootRegion rootSSA reachable attached regions run
  · exact Pattern.compile_moduleRefinement_of_unreachable rule rootIn moduleCode sourceVerified rootRooted
      reachable attached regions run

/-- A valid pattern's successful compilation refines its original verified module,
including when the root lies in unreachable code. -/
theorem Pattern.Valid.compile_moduleRefinement
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr} {region : RegionPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx := by
  obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp rootRegion
  have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
  have targetVerified := valid.compile_preservesVerified rootIn moduleCode sourceVerified rootRooted
    rootRegion rootSSA attached regions run
  exact valid.compile_moduleRefinement_of_verified_output rootIn moduleCode sourceVerified targetVerified
    rootRooted rootRegion rootSSA attached regions run

end Veir.Puddle.CTree
