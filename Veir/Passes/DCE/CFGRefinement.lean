module

public import Veir.Passes.DCE.OperationRefinement
public import Veir.Interpreter.CTreeRefinement.Iteration

import all Veir.Interfaces.SideEffectInterfaces
import all Veir.GlobalOpInfo
import all Veir.Passes.DCE.Structure
import all Veir.Interpreter.VariableState
import all Veir.Passes.DCE.StateRefinement

public section

open CTree

namespace Veir.CTree

/-- Continue a closed CFG step after an operation produces its control-flow action. -/
@[expose]
def interpretCFGTreeContinue {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (action : Option ControlFlowAction)
    (opIn : op.InBounds ctx.raw := by grind) :
    Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)) := do
  match action with
  | some (.return results) => return .inr (state, results)
  | some (.branch args dest) =>
    if h : dest.InBounds ctx.raw then
      return .inl (.inl (⟨dest, h⟩, args), state)
    else fail
  | none =>
    rlet some nextOp := op.getNextOp ctx.raw | fail
    return .inl (.inr ⟨nextOp, by grind⟩, state)

/-- The closed version of one CFG step, using the closed operation interpreter. -/
@[expose]
def interpretCFGTreeStep {ctx : WfIRContext OpCode}
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)) := do
  match location with
  | .inl (⟨block, blockIn⟩, values) =>
    if values.size != block.getNumArguments! ctx.raw then fail else
    let some variables := state.variables.setArgumentValues? block values blockIn | fail
    rlet some firstOp := block.getFirstOp ctx.raw | fail
    return .inl (.inr ⟨firstOp, by grind⟩, ⟨variables, state.memory⟩)
  | .inr ⟨op, opIn⟩ =>
    let (state, action) ← interpretOperationTree op state opIn
    interpretCFGTreeContinue op state action

/-- A closed CFG loop, separating unbounded control flow from finite operation trees. -/
@[expose]
def interpretCFGTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Array RuntimeValue) := do
  rlet some firstBlock := region.getFirstBlock ctx.raw | fail
  _root_.CTree.iter (fun (location, state) => interpretCFGTreeStep location state)
    (.inl (⟨firstBlock, by grind⟩, values), state)

end Veir.CTree

namespace Veir.DCE

/-- CFG locations agree on block entries and use an explicit relation on operation
pointers, allowing a source successor to precede deleted operations. -/
@[expose]
def CFGLocationRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (operations : OperationPtr → OperationPtr → Prop) :
    CTree.interpretCFG.StateLocation sourceCtx → CTree.interpretCFG.StateLocation targetCtx → Prop
  | .inl (⟨sourceBlock, _⟩, sourceValues), .inl (⟨targetBlock, _⟩, targetValues) =>
    sourceBlock = targetBlock ∧ RuntimeValue.arrayIsRefinedBy sourceValues targetValues
  | .inr ⟨sourceOp, _⟩, .inr ⟨targetOp, _⟩ => operations sourceOp targetOp
  | _, _ => False

/-- Live interpreter states at related CFG locations. -/
@[expose]
def CFGStateRefinesOn {sourceCtx targetCtx : WfIRContext OpCode}
    (live : ValuePtr → Prop) (operations : OperationPtr → OperationPtr → Prop)
    (source : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx)
    (target : CTree.interpretCFG.StateLocation targetCtx × InterpreterState targetCtx) : Prop :=
  CFGLocationRefines operations source.1 target.1 ∧ StatesRefineOn live source.2 target.2

/-- Returned CFG values and the live final state refine together. -/
@[expose]
def CFGReturnRefinesOn {sourceCtx targetCtx : WfIRContext OpCode} (live : ValuePtr → Prop)
    (source : InterpreterState sourceCtx × Array RuntimeValue)
    (target : InterpreterState targetCtx × Array RuntimeValue) : Prop :=
  StatesRefineOn live source.1 target.1 ∧ RuntimeValue.arrayIsRefinedBy source.2 target.2

/-- Lift related operation actions to CFG transitions. The next-pointer hypothesis
is separate so erasure proofs can supply a skipped-chain relation. -/
theorem interpretCFGTreeContinue_refinesOn
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {source : InterpreterState sourceCtx} {target : InterpreterState targetCtx}
    {sourceAction targetAction : Option ControlFlowAction}
    (live : ValuePtr → Prop) (operations : OperationPtr → OperationPtr → Prop)
    (hstate : StatesRefineOn live source target)
    (haction : ControlFlowAction.optionIsRefinedBy sourceAction targetAction)
    (hblocks : ∀ block : BlockPtr, block.InBounds sourceCtx.raw → block.InBounds targetCtx.raw)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (hnext : ∀ nextSource, sourceOp.getNextOp sourceCtx.raw = some nextSource →
      ∃ nextTarget, targetOp.getNextOp targetCtx.raw = some nextTarget ∧
        operations nextSource nextTarget) :
    Tree.Refines (Sum.LiftRel (CFGStateRefinesOn live operations) (CFGReturnRefinesOn live))
      (CTree.interpretCFGTreeContinue sourceOp source sourceAction sourceIn)
      (CTree.interpretCFGTreeContinue targetOp target targetAction targetIn) := by
  cases sourceAction with
  | none =>
    cases targetAction with
    | some action => cases haction
    | none =>
      simp only [CTree.interpretCFGTreeContinue]
      split
      · rename_i nextSource hsource
        obtain ⟨nextTarget, htarget, hrelated⟩ := hnext nextSource hsource
        split
        · rename_i nextTarget' htarget'
          have : nextTarget' = nextTarget := by grind
          subst nextTarget'
          exact (Tree.refines_pure _ _ _).mpr (.inl ⟨hrelated, hstate⟩)
        · grind
      · exact Tree.refines_fail _ _
  | some sourceAction =>
    cases targetAction with
    | none => cases haction
    | some targetAction =>
      cases sourceAction <;> cases targetAction <;>
        simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] at haction
      · exact (Tree.refines_pure _ _ _).mpr (.inr ⟨hstate, haction⟩)
      · obtain ⟨hdest, hvalues⟩ := haction
        subst hdest
        simp only [CTree.interpretCFGTreeContinue]
        split
        · rename_i hsource
          simp only [dite_eq_left (hblocks _ hsource)]
          exact (Tree.refines_pure _ _ _).mpr (.inl ⟨⟨rfl, hvalues⟩, hstate⟩)
        · exact Tree.refines_fail _ _

/-- Related block arguments can be bound in the target whenever binding succeeds in
source, provided the block's argument metadata is unchanged. -/
theorem setBlockArguments_refineOn
    {sourceCtx targetCtx : WfIRContext OpCode} {block : BlockPtr}
    {source nextSource : VariableState sourceCtx} {target : VariableState targetCtx}
    {live : ValuePtr → Prop} {sourceValues targetValues : Array RuntimeValue}
    {sourceIn : block.InBounds sourceCtx.raw} {targetIn : block.InBounds targetCtx.raw}
    (hstate : VariablesRefineOn live source target)
    (hcount : block.getNumArguments! targetCtx.raw = block.getNumArguments! sourceCtx.raw)
    (htypes : ∀ index, index < block.getNumArguments! sourceCtx.raw →
      (block.getArgument index : ValuePtr).getType! targetCtx.raw =
        (block.getArgument index : ValuePtr).getType! sourceCtx.raw)
    (hsize : sourceValues.size = block.getNumArguments! sourceCtx.raw)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hsource : source.setArgumentValues? block sourceValues sourceIn = some nextSource) :
    ∃ nextTarget, target.setArgumentValues? block targetValues targetIn = some nextTarget ∧
      VariablesRefineOn live nextSource nextTarget := by
  have hsourceConforms :=
    (VariableState.setArgumentValues?_isSome_iff_conforms source).mpr ⟨nextSource, hsource⟩
  have htargetConforms : ∀ index, index < block.getNumArguments! targetCtx.raw →
      (targetValues[index]!).Conforms ((block.getArgument index : ValuePtr).getType! targetCtx.raw) := by
    intro index hindex
    have hsourceIndex : index < block.getNumArguments! sourceCtx.raw := by omega
    rw [htypes index hsourceIndex]
    exact conforms_of_refines (hvalues.2 index (by omega)) (hsourceConforms index hsourceIndex)
  obtain ⟨nextTarget, htarget⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms target).mp htargetConforms
  exact ⟨nextTarget, htarget,
    variablesRefineOn_setArguments hstate hcount hsize hvalues hsource htarget⟩

end Veir.DCE

namespace Veir.DCE

/-- A block entry preserves live-state refinement while binding related arguments.
The first-operation relation can account for a finite chain of deleted operations. -/
theorem interpretCFGTreeStep_block_refinesOn
    {sourceCtx targetCtx : WfIRContext OpCode} (block : BlockPtr)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : block.InBounds sourceCtx.raw) (targetIn : block.InBounds targetCtx.raw)
    (sourceValues targetValues : Array RuntimeValue)
    (live : ValuePtr → Prop) (operations : OperationPtr → OperationPtr → Prop)
    (hstate : StatesRefineOn live source target)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hcount : block.getNumArguments! targetCtx.raw = block.getNumArguments! sourceCtx.raw)
    (htypes : ∀ index, index < block.getNumArguments! sourceCtx.raw →
      (block.getArgument index : ValuePtr).getType! targetCtx.raw =
        (block.getArgument index : ValuePtr).getType! sourceCtx.raw)
    (hfirst : ∀ firstSource, block.getFirstOp sourceCtx.raw = some firstSource →
      ∃ firstTarget, block.getFirstOp targetCtx.raw = some firstTarget ∧
        operations firstSource firstTarget) :
    Tree.Refines (Sum.LiftRel (CFGStateRefinesOn live operations) (CFGReturnRefinesOn live))
      (CTree.interpretCFGTreeStep (.inl (⟨block, sourceIn⟩, sourceValues)) source)
      (CTree.interpretCFGTreeStep (.inl (⟨block, targetIn⟩, targetValues)) target) := by
  simp only [CTree.interpretCFGTreeStep]
  split
  · exact Tree.refines_fail _ _
  · rename_i hsize
    have hsize' : sourceValues.size = block.getNumArguments! sourceCtx.raw := by simpa using hsize
    have htargetSize : (targetValues.size != block.getNumArguments! targetCtx.raw) = false := by
      simp only [hcount, ← hsize', ← hvalues.1, bne_self_eq_false]
    simp only [htargetSize, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i nextSource hsetSource
      obtain ⟨nextTarget, hsetTarget, hvariables⟩ :=
        setBlockArguments_refineOn (targetIn := targetIn) hstate.2 hcount htypes hsize' hvalues hsetSource
      simp only [hsetTarget]
      split
      · rename_i firstSource hfirstSource
        obtain ⟨firstTarget, hfirstTarget, hrelated⟩ := hfirst firstSource hfirstSource
        split
        · rename_i firstTarget' hfirstTarget'
          have : firstTarget' = firstTarget := by grind
          subst firstTarget'
          exact (Tree.refines_pure _ _ _).mpr (.inl ⟨hrelated, hstate.1, hvariables⟩)
        · grind
      · exact Tree.refines_fail _ _
    · exact Tree.refines_fail _ _

/-- Match a surviving operation's CFG transition. This combines operand/result
refinement with return, branch, and sequential successor transitions. -/
theorem interpretCFGTreeStep_operation_refinesOn
    {sourceCtx targetCtx : WfIRContext OpCode} (erases : Erasures sourceCtx targetCtx)
    (operation : OperationPtr) (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : operation.InBounds targetCtx.raw)
    (live : ValuePtr → Prop) (operations : OperationPtr → OperationPtr → Prop)
    (hstate : StatesRefineOn live source target)
    (hsourceIn : ∀ value, live value → value.InBounds sourceCtx.raw)
    (htargetIn : ∀ value, live value → value.InBounds targetCtx.raw)
    (hlive : ∀ value ∈ operation.getOperands! sourceCtx.raw, live value)
    (hnext : ∀ nextSource, operation.getNextOp sourceCtx.raw = some nextSource →
      ∃ nextTarget, operation.getNextOp targetCtx.raw = some nextTarget ∧
        operations nextSource nextTarget) :
    Tree.Refines (Sum.LiftRel (CFGStateRefinesOn live operations) (CFGReturnRefinesOn live))
      (CTree.interpretCFGTreeStep (.inr ⟨operation, sourceIn⟩) source)
      (CTree.interpretCFGTreeStep (.inr ⟨operation, targetIn⟩) target) := by
  simp only [CTree.interpretCFGTreeStep]
  apply Tree.refines_bind
    (interpretOperationTree_refinesOn_of_erasures erases operation source target sourceIn targetIn
      live hstate hsourceIn htargetIn hlive)
  rintro ⟨nextSource, sourceAction⟩ ⟨nextTarget, targetAction⟩ ⟨hstates, hactions⟩
  exact interpretCFGTreeContinue_refinesOn live operations hstates hactions
    (fun block => (erases.block_inBounds_iff block).mpr) sourceIn targetIn hnext

end Veir.DCE

namespace Veir.DCE

/-- A successful step at a discarded operation can only advance to its original
successor. It preserves memory and all final live definitions. -/
theorem interpretCFGTreeStep_discarded_frame
    {sourceCtx targetCtx : WfIRContext OpCode} (operation : OperationPtr)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : operation.InBounds sourceCtx.raw) (live : ValuePtr → Prop)
    (hstate : StatesRefineOn live source target)
    (hdiscarded : ∀ value, live value → value ∉ operation.getResults! sourceCtx.raw)
    (hwrite : (OpCode.getEffects (operation.getOpType! sourceCtx.raw)
      (operation.getProperties! sourceCtx.raw (operation.getOpType! sourceCtx.raw))).writes = false)
    (hallocate : (OpCode.getEffects (operation.getOpType! sourceCtx.raw)
      (operation.getProperties! sourceCtx.raw (operation.getOpType! sourceCtx.raw))).allocates = false)
    (hterminator : OpCode.isTerminator (operation.getOpType! sourceCtx.raw) = false)
    (result : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) ⊕
      (InterpreterState sourceCtx × Array RuntimeValue))
    (hrun : PureOrErr.CanInterpretTo
      (CTree.interpretCFGTreeStep (.inr ⟨operation, sourceIn⟩) source) (.ok result)) :
    ∃ (next : OperationPtr) (nextIn : next.InBounds sourceCtx.raw)
      (nextState : InterpreterState sourceCtx),
      operation.getNextOp sourceCtx.raw = some next ∧
      result = .inl (.inr ⟨next, nextIn⟩, nextState) ∧ StatesRefineOn live nextState target := by
  simp only [CTree.interpretCFGTreeStep, Bind.bind, PureOrErr.CanInterpretTo.bind_ok_iff] at hrun
  obtain ⟨⟨nextState, action⟩, hop, hcontinue⟩ := hrun
  obtain ⟨hstate', rfl⟩ := interpretOperationTree_discarded_frame operation source target sourceIn live
    hstate hdiscarded hwrite hallocate hterminator nextState action hop
  simp only [CTree.interpretCFGTreeContinue] at hcontinue
  split at hcontinue
  · rename_i next hnext
    simp only [PureOrErr.CanInterpretTo.pure_iff, Interp.ok.injEq] at hcontinue
    exact ⟨next, by grind, nextState, hnext, hcontinue, hstate'⟩
  · simp at hcontinue

/-- Every closed CFG body consists of finite opcode execution and finite checks. -/
theorem interpretCFGTreeStep_pureOrErr {ctx : WfIRContext OpCode}
    (location : CTree.interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    PureOrErr (CTree.interpretCFGTreeStep location state) := by
  cases location with
  | inl block =>
    rcases block with ⟨⟨block, blockIn⟩, values⟩
    simp only [CTree.interpretCFGTreeStep]
    split
    · exact PureOrErr.fail_tree
    · split
      · split
        · exact PureOrErr.pure_tree _
        · exact PureOrErr.fail_tree
      · exact PureOrErr.fail_tree
  | inr operation =>
    rcases operation with ⟨operation, operationIn⟩
    simp only [CTree.interpretCFGTreeStep]
    apply PureOrErr.bind
    · exact CTree.interpretOperationTree_pureOrErr _ _ _
    · rintro ⟨nextState, action⟩
      cases action with
      | none =>
        simp only [CTree.interpretCFGTreeContinue]
        split
        · exact PureOrErr.pure_tree _
        · exact PureOrErr.fail_tree
      | some action =>
        cases action with
        | «return» values => exact PureOrErr.pure_tree _
        | branch values destination =>
          simp only [CTree.interpretCFGTreeContinue]
          split
          · exact PureOrErr.pure_tree _
          · exact PureOrErr.fail_tree

end Veir.DCE

namespace Veir.DCE

/-- A deleted operation has no results among the final context's live values. -/
theorem deleted_results_not_live
    {sourceCtx targetCtx : WfIRContext OpCode}
    (operation : OperationPtr) (deleted : ¬ operation.InBounds targetCtx.raw)
    (value : ValuePtr) (live : value.InBounds targetCtx.raw) :
    value ∉ operation.getResults! sourceCtx.raw := by
  intro hresult
  obtain ⟨index, _, rfl⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hresult
  exact deleted (by grind)

end Veir.DCE

namespace Veir.DCE

/-- Specialize the discarded-step frame theorem to the values surviving actual
DCE erasures; eligibility follows from the original operation metadata. -/
theorem interpretCFGTreeStep_deleted_frame
    {sourceCtx targetCtx : WfIRContext OpCode} (erases : Erasures sourceCtx targetCtx)
    (operation : OperationPtr) (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : operation.InBounds sourceCtx.raw) (deleted : ¬ operation.InBounds targetCtx.raw)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target)
    (result : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) ⊕
      (InterpreterState sourceCtx × Array RuntimeValue))
    (hrun : PureOrErr.CanInterpretTo
      (CTree.interpretCFGTreeStep (.inr ⟨operation, sourceIn⟩) source) (.ok result)) :
    ∃ (next : OperationPtr) (nextIn : next.InBounds sourceCtx.raw)
      (nextState : InterpreterState sourceCtx),
      operation.getNextOp sourceCtx.raw = some next ∧
      result = .inl (.inr ⟨next, nextIn⟩, nextState) ∧
      StatesRefineOn (fun value => value.InBounds targetCtx.raw) nextState target := by
  have heligible := erases.deleted_eligible operation sourceIn deleted
  rcases heligible with ⟨hregions, hwrite, hallocate, hterminator⟩
  simp only [OperationPtr.getEffects, hregions, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte] at hwrite hallocate
  apply interpretCFGTreeStep_discarded_frame operation source target sourceIn _ hstate
    (deleted_results_not_live operation deleted) _ _ _ result hrun
  · simpa [HasOpInfo.getEffects, instHasOpInfoOpCode] using hwrite
  · simpa [HasOpInfo.getEffects, instHasOpInfoOpCode] using hallocate
  · simpa [HasOpInfo.isTerminator, instHasOpInfoOpCode] using hterminator

end Veir.DCE
