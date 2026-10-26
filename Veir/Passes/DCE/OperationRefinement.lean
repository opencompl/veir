module

public import Veir.Passes.DCE.StateRefinement
public import Veir.Passes.DCE.Structure
public import Veir.Interpreter.CTreeInterpreter
public import Veir.Interpreter.CTreeRefinement.InflationEffects

import all Veir.Passes.DCE.StateRefinement
import all Veir.Interpreter.VariableState

public section

namespace Veir.CTree

/-- Execute an operation as a closed tree. Region-call effects are absent from
opcode semantics; the ordinary region interpreter embeds this tree in its effect type. -/
@[expose]
def interpretOperationTree (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | fail
  let opType := op.getOpType! ctx.raw
  let (results, memory, action) ← Tree.inflate (Tree.inflate (interpretOpTree opType
    (op.getProperties! ctx.raw opType) (op.getResultTypes! ctx.raw) operands
    (op.getSuccessors! ctx.raw) state.memory))
  let some variables := state.variables.setResultValues? op results opIn | fail
  return (⟨variables, memory⟩, action)

/-- Operand lookup and checked result binding do not introduce unbounded execution. -/
theorem interpretOperationTree_pureOrErr (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw := by grind) :
    PureOrErr (interpretOperationTree op state opIn) := by
  simp only [interpretOperationTree]
  split
  · apply PureOrErr.bind
    · exact Tree.pureOrErr_inflate (Tree.pureOrErr_inflate (interpretOpTree_pureOrErr _ _ _ _ _ _))
    · intro result
      split
      · exact PureOrErr.pure_tree _
      · exact PureOrErr.fail_tree
  · exact PureOrErr.fail_tree

end Veir.CTree

namespace Veir.DCE

/-- Lift opcode monotonicity through operand lookup and the checked result setters,
relating only definitions that survive in the target context. -/
theorem interpretOperationTree_refinesOn
    {sourceCtx targetCtx : WfIRContext OpCode} (operation : OperationPtr)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : operation.InBounds targetCtx.raw)
    (live : ValuePtr → Prop)
    (hstate : StatesRefineOn live source target)
    (hsourceIn : ∀ value, live value → value.InBounds sourceCtx.raw)
    (htargetIn : ∀ value, live value → value.InBounds targetCtx.raw)
    (hopcode : operation.getOpType! targetCtx.raw = operation.getOpType! sourceCtx.raw)
    (hproperties : ∀ opcode : OpCode,
      operation.getProperties! targetCtx.raw opcode = operation.getProperties! sourceCtx.raw opcode)
    (htypes : operation.getResultTypes! targetCtx.raw = operation.getResultTypes! sourceCtx.raw)
    (hsuccessors : operation.getSuccessors! targetCtx.raw = operation.getSuccessors! sourceCtx.raw)
    (hoperands : operation.getOperands! targetCtx.raw = operation.getOperands! sourceCtx.raw)
    (hlive : ∀ value ∈ operation.getOperands! sourceCtx.raw, live value) :
    Tree.Refines
      (fun sourceResult targetResult => StatesRefineOn live sourceResult.1 targetResult.1 ∧
        ControlFlowAction.optionIsRefinedBy sourceResult.2 targetResult.2)
      (CTree.interpretOperationTree operation source sourceIn)
      (CTree.interpretOperationTree operation target targetIn) := by
  cases hsource : source.variables.getOperandValues operation with
  | none =>
    simp only [CTree.interpretOperationTree, hsource]
    exact Tree.refines_fail _ _
  | some sourceValues =>
    obtain ⟨targetValues, htarget, hvalues⟩ :=
      getOperandValues_refineOn hstate.2 hoperands hlive hsource
    simp only [CTree.interpretOperationTree, hsource, htarget, hproperties,
      htypes, hsuccessors]
    rw [hopcode]
    apply Tree.refines_bind
      (Tree.refines_inflate (Tree.refines_inflate
        (Tree.Refinement.operation_monotonicity _ _ _ _ sourceValues targetValues
          source.memory target.memory hvalues hstate.1)))
    rintro ⟨sourceResults, sourceMemory, sourceAction⟩
      ⟨targetResults, targetMemory, targetAction⟩ ⟨hresults, hmemory, haction⟩
    cases hsetSource : source.variables.setResultValues? operation sourceResults sourceIn with
    | none =>
      exact Tree.refines_fail _ _
    | some sourceVariables =>
      have hconformsSource := RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hsetSource
      have hconformsTarget := arrayConforms_of_refines hresults hconformsSource
      rw [← htypes] at hconformsTarget
      obtain ⟨targetVariables, hsetTarget⟩ :=
        (VariableState.setResultValues?_isSome_iff_conforms target.variables targetIn).mp hconformsTarget
      simp only [hsetTarget]
      apply (Tree.refines_pure _ _ _).mpr
      exact ⟨⟨hmemory, variablesRefineOn_setResults hstate.2 hsourceIn htargetIn
        hresults hsetSource hsetTarget⟩, haction⟩

/-- Apply the live-state lifting theorem to an operation surviving the actual DCE deletions. -/
theorem interpretOperationTree_refinesOn_of_erasures
    {sourceCtx targetCtx : WfIRContext OpCode} (erases : Erasures sourceCtx targetCtx)
    (operation : OperationPtr) (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : operation.InBounds targetCtx.raw)
    (live : ValuePtr → Prop) (hstate : StatesRefineOn live source target)
    (hsourceIn : ∀ value, live value → value.InBounds sourceCtx.raw)
    (htargetIn : ∀ value, live value → value.InBounds targetCtx.raw)
    (hlive : ∀ value ∈ operation.getOperands! sourceCtx.raw, live value) :
    Tree.Refines
      (fun sourceResult targetResult => StatesRefineOn live sourceResult.1 targetResult.1 ∧
        ControlFlowAction.optionIsRefinedBy sourceResult.2 targetResult.2)
      (CTree.interpretOperationTree operation source sourceIn)
      (CTree.interpretOperationTree operation target targetIn) :=
  interpretOperationTree_refinesOn operation source target sourceIn targetIn live hstate
    hsourceIn htargetIn (erases.getOpType operation targetIn)
    (erases.getProperties operation targetIn) (erases.getResultTypes operation targetIn)
    (erases.getSuccessors operation targetIn) (erases.getOperands operation targetIn) hlive

/-- Executing a discarded operation preserves every live definition and the memory
relation. The memory/control property is proved from the opcode metadata. -/
theorem interpretOperationTree_discarded_frame
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
    (nextSource : InterpreterState sourceCtx) (action : Option ControlFlowAction)
    (hrun : PureOrErr.CanInterpretTo (CTree.interpretOperationTree operation source sourceIn)
      (.ok (nextSource, action))) :
    StatesRefineOn live nextSource target ∧ action = none := by
  cases hoperands : source.variables.getOperandValues operation with
  | none => simp [CTree.interpretOperationTree, hoperands] at hrun
  | some operands =>
    simp only [CTree.interpretOperationTree, hoperands, Bind.bind,
      PureOrErr.CanInterpretTo.bind_ok_iff] at hrun
    rcases hrun with ⟨⟨results, memory, rawAction⟩, hraw, hnext⟩
    have hfinite := CTree.interpretOpTree_pureOrErr (operation.getOpType! sourceCtx.raw)
      (operation.getProperties! sourceCtx.raw (operation.getOpType! sourceCtx.raw))
      (operation.getResultTypes! sourceCtx.raw) operands (operation.getSuccessors! sourceCtx.raw) source.memory
    have hraw := (Tree.canInterpretTo_inflate_iff hfinite _).mp
      ((Tree.canInterpretTo_inflate_iff (Tree.pureOrErr_inflate hfinite) _).mp hraw)
    cases hset : source.variables.setResultValues? operation results sourceIn with
    | none => simp [hset] at hnext
    | some variables =>
      simp only [hset, PureOrErr.CanInterpretTo.pure_iff, Interp.ok.injEq, Prod.mk.injEq] at hnext
      rcases hnext with ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := CTree.interpretOpTree_preserves_memory_and_control _ _ _ _ _ _ _ _ _
        hwrite hallocate hterminator hraw
      exact ⟨⟨hstate.1, variablesRefineOn_setDiscardedResults hstate.2 hdiscarded hset⟩, rfl⟩

end Veir.DCE
