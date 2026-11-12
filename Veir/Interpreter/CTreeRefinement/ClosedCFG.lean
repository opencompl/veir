module

public import Veir.Interpreter.CTreeInterpreter

public section

/-!
# The closed CFG interpreter

`interpretRegion` runs a region's CFG in `RegionTree`, whose effects include region calls, and
closes them with `CTree.mrec`. The event type of a `RegionTree` depends on its context, so two
trees from different contexts cannot be compared with `CTree.Sim` before `mrec` removes the
region calls.

No operation calls a region, so the CFG loop can be run as a closed `Tree` instead. This file
defines that closed loop. It keeps the silent steps of the ordinary interpreter: `inflate` is the
event-handler layer that `interpretOp` and `mrec` each wrap around a tree.
-/

open CTree

namespace Veir.CTree

/-- Re-emit the events of a closed tree with the ordinary CTree event interpreter, keeping the
silent steps it inserts. -/
@[expose]
def inflate (tree : Tree α) : Tree α :=
  CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree

/-- Interpret an operation as a closed tree, with the two event-handler layers of `interpretOp`. -/
@[expose]
def interpretOperationTree (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | fail
  let opType := op.getOpType ctx.raw inBounds
  let (resultValues, mem, action) ← inflate (inflate (interpretOp' opType
    (op.getProperties ctx.raw opType) (op.getResultTypes ctx.raw) operands
    (op.getSuccessors ctx.raw) state.memory (op.getRegions ctx.raw)))
  let some variables := state.variables.setResultValues? op resultValues inBounds | fail
  return (⟨variables, mem⟩, action)

/-- Continue a closed CFG step after an operation produced its control-flow action. -/
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

/-- One closed CFG step: enter a block, or run an operation. -/
@[expose]
def interpretCFGTreeStep {ctx : WfIRContext OpCode}
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)) := do
  match location with
  | .inl (⟨block, blockIn⟩, values) =>
    if values.size != block.getNumArguments ctx.raw then fail else
    let some variables := state.variables.setArgumentValues? block values | fail
    rlet some firstOp := block.getFirstOp ctx.raw | fail
    return .inl (.inr ⟨firstOp, by grind⟩, ⟨variables, state.memory⟩)
  | .inr ⟨op, opIn⟩ =>
    let (state, action) ← interpretOperationTree op state opIn
    interpretCFGTreeContinue op state action

/-- The closed CFG loop of a region. -/
@[expose]
def interpretCFGTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw := by grind) :
    Tree (InterpreterState ctx × Array RuntimeValue) := do
  rlet some firstBlock := region.getFirstBlock ctx.raw | fail
  _root_.CTree.iter (fun (location, state) => interpretCFGTreeStep location state)
    (.inl (⟨firstBlock, by grind⟩, values), state)

end Veir.CTree
