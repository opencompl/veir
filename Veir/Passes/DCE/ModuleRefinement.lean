module

public import Veir.Passes.DCE.Structure
public import Veir.Passes.DCE.FunctionRefinement
public import Veir.Passes.DCE.CFGCompleteRefinement
public import Veir.Interpreter.CTreeRefinement.Program
public import Veir.Verifier

import all Veir.Passes.DCE.dce
import all Veir.Passes.DCE.Erasure
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Passes.DCE.StateRefinement

public section

namespace Veir.DCE

/-- The executable transformation produces exactly the deletion sequence
established for the greedy driver. -/
theorem transform_erasures {source target : WfIRContext OpCode}
    (success : DCEPass.transform source = some target) : Erasures source target := by
  apply applyInContext_erasures source target
  simpa only [DCEPass.transform, pattern] using success

/-- DCE preserves the name and module membership of every verified source function.
Verification guarantees a body region, so the function itself cannot be deleted. -/
theorem Erasures.topLevelFunction_survives {source target : WfIRContext OpCode}
    (erases : Erasures source target) {root moduleOp function : OperationPtr}
    (verified : source.Verified root) (functionIn : function.InBounds source.raw)
    {name : StringAttr}
    (topLevel : function.IsTopLevelFuncWithName moduleOp source.raw name) :
    function.InBounds target.raw ∧
      function.IsTopLevelFuncWithName moduleOp target.raw name := by
  have functionVerified :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified functionIn
  have regions := (functionVerified.func_func topLevel.isFunc).2.2.2
  have survives := erases.region_bearing_survives function functionIn (by omega)
  have properties : function.getProperties! target.raw Func.func =
      function.getProperties! source.raw Func.func :=
    erases.survivor_observation (fun ctx op => op.getProperties! ctx Func.func)
      (fun _ _ _ _ _ hs => by simp [hs]) function survives
  refine ⟨survives, ?_⟩
  exact ⟨(erases.getOpType function survives).trans topLevel.isFunc,
    topLevel.hasName.trans (congrArg (·.sym_name) properties).symm,
    (erases.getParentOp function survives).trans topLevel.isTopLevel⟩

/-- Lift refinement of surviving function bodies to the whole module relation. -/
theorem Erasures.isModuleRefinedBy_of_functions {source target : WfIRContext OpCode}
    (erases : Erasures source target) {root moduleOp : OperationPtr}
    (verified : source.Verified root)
    (functions : ∀ (function : OperationPtr)
      (sourceIn : function.InBounds source.raw) (targetIn : function.InBounds target.raw),
      function.getOpType! source.raw = .func .func →
      Tree.Refinement.OperationPtr.isRefinedByAsFunction function source function target
        sourceIn targetIn) :
    Tree.Refinement.OperationPtr.isModuleRefinedBy moduleOp source moduleOp target := by
  intro function sourceIn name topLevel
  obtain ⟨targetIn, targetTopLevel⟩ :=
    erases.topLevelFunction_survives verified sourceIn topLevel
  exact ⟨function, targetIn, targetTopLevel,
    functions function sourceIn targetIn topLevel.isFunc⟩

/-- Package a direct region simulation into the whole-program relation. -/
theorem Erasures.isModuleRefinedBy_of_closedCFG {source target : WfIRContext OpCode}
    (erases : Erasures source target) {root moduleOp : OperationPtr}
    (verified : source.Verified root)
    (regions : ∀ (region : RegionPtr) (sourceIn : region.InBounds source.raw)
      (targetIn : region.InBounds target.raw)
      (sourceValues targetValues : Array RuntimeValue)
      (sourceState : InterpreterState source) (targetState : InterpreterState target),
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      StatesRefineOn (fun value => value.InBounds target.raw) sourceState targetState →
      Tree.Refines (CFGReturnRefinesOn (fun value => value.InBounds target.raw))
        (CTree.interpretCFGTree region sourceValues sourceState sourceIn)
        (CTree.interpretCFGTree region targetValues targetState targetIn)) :
    Tree.Refinement.OperationPtr.isModuleRefinedBy moduleOp source moduleOp target := by
  apply erases.isModuleRefinedBy_of_functions verified
  intro function sourceIn targetIn sourceType
  have targetType := (erases.getOpType function targetIn).trans sourceType
  have functionVerified :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified sourceIn
  have sourceCount := (functionVerified.func_func sourceType).2.2.2
  have targetCount := (erases.getNumRegions function targetIn).trans sourceCount
  cases sourceView : FunctionOp.of? function source.raw with
  | none =>
    unfold FunctionOp.of? at sourceView
    split at sourceView
    · cases sourceView
    · rename_i noInterface
      have hasInterface := congrArg
        (fun opcode : OpCode => (HasOpInfo.functionInterface? opcode).isSome) sourceType
      rw [noInterface] at hasInterface
      cases hasInterface
  | some sourceFunction =>
    cases targetView : FunctionOp.of? function target.raw with
    | none =>
      unfold FunctionOp.of? at targetView
      split at targetView
      · cases targetView
      · rename_i noInterface
        have hasInterface := congrArg
          (fun opcode : OpCode => (HasOpInfo.functionInterface? opcode).isSome) targetType
        rw [noInterface] at hasInterface
        cases hasInterface
    | some targetFunction =>
      apply (Tree.Refinement.OperationPtr.isRefinedByAsFunction_iff
        sourceView targetView sourceIn targetIn).mpr
      have sourceCount' : function.getNumRegions source.raw sourceIn = 1 := by grind
      have targetCount' : function.getNumRegions target.raw targetIn = 1 := by grind
      apply functionRefines_of_closedCFG sourceFunction targetFunction sourceIn targetIn
        sourceCount' targetCount' (fun value => value.InBounds target.raw)
      intro sourceValues targetValues memory related
      have bodies : sourceFunction.getFunctionBody sourceIn (by omega) =
          targetFunction.getFunctionBody targetIn (by omega) := by
        have sameRegion := erases.getRegion function targetIn 0
        grind [FunctionOp.getFunctionBody]
      have sourceBodyIn : (targetFunction.getFunctionBody targetIn (by omega)).InBounds
          source.raw := by
        rw [← bodies]
        grind [FunctionOp.getFunctionBody]
      have refinement := regions (targetFunction.getFunctionBody targetIn (by omega))
        sourceBodyIn (by grind [FunctionOp.getFunctionBody]) sourceValues targetValues
        (⟨.empty source, memory⟩ : InterpreterState source)
        (⟨.empty target, memory⟩ : InterpreterState target) related
        ⟨Tree.Refinement.MemoryState.isRefinedBy_refl memory,
          variablesRefineOn_empty source target _⟩
      simpa only [bodies] using refinement

/-- Every finite sequence of DCE deletions refines the whole verified source module.
The proof compares the original and final CFGs directly. -/
theorem Erasures.isModuleRefinedBy {source target : WfIRContext OpCode}
    (erases : Erasures source target) {moduleOp : OperationPtr}
    (verified : source.Verified moduleOp) :
    Tree.Refinement.OperationPtr.isModuleRefinedBy moduleOp source moduleOp target :=
  erases.isModuleRefinedBy_of_closedCFG verified erases.interpretCFGTree_refines

end Veir.DCE

namespace Veir

/-- Whole-program correctness of the complete greedy DCE transformation under
CTree semantics. Successful outputs refine the verified input module, including
refining arguments and final memory, without a semantic transitivity axiom. -/
theorem DCEPass.transform_isModuleRefinedBy {source target : WfIRContext OpCode}
    {moduleOp : OperationPtr} (verified : source.Verified moduleOp)
    (success : DCEPass.transform source = some target) :
    Tree.Refinement.OperationPtr.isModuleRefinedBy moduleOp source moduleOp target :=
  (DCE.transform_erasures success).isModuleRefinedBy verified

/-- A successful pure transformation is exactly the context returned by the
registered DCE pass, independently of its unused options and root argument. -/
theorem DCEPass.run_eq_of_transform {source target : WfIRContext OpCode}
    (success : DCEPass.transform source = some target)
    (options : PassOptions) (root : OperationPtr) (rootIn : root.InBounds source.raw) :
    DCEPass.run options source root rootIn = pure target := by
  simp only [DCEPass, DCEPass.impl, success]

end Veir
