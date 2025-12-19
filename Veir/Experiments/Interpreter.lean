import Buffed.Prelude
import Veir.IR.Basic
import Veir.Rewriter
import Veir.Printer
import Veir.ForLean
import Veir.WellFormedness
import Veir.PatternRewriter

namespace Veir

abbrev InterpreterValue := UInt64

structure InterpreterState where
  variables : Std.HashMap ValuePtr InterpreterValue

def InterpreterState.setVar (state : InterpreterState) (var : ValuePtr) (val : InterpreterValue) : Option InterpreterState :=
  if state.variables.contains var then
    none
  else
    some { state with variables := state.variables.insert var val }

def InterpreterState.getVar (state : InterpreterState) (var : ValuePtr) : Option InterpreterValue :=
  state.variables[var]?

def InterpreterState.empty : InterpreterState :=
  { variables := Std.HashMap.emptyWithCapacity 8 }

inductive InterpreterAction where
  | return (vals : Array InterpreterValue)
  | continue

def interpretOp (ctx : IRContext) (opPtr : OperationPtr) (opPtrInBounds : opPtr.InBounds ctx := by grind) (state : InterpreterState) : Option (InterpreterState × InterpreterAction) :=
  let op := opPtr.get ctx (by grind)
  match op.opType with
  | 1 => do -- arith.constant
    let valueAttrPtr := op.properties
    let result := { op := opPtr, index := 0 }
    let newState ← state.setVar (ValuePtr.opResult result) op.properties
    return (newState, .Continue)
  | 2 => do -- arith.addi
    let lhs ← op.operands[0]?.map (·.value) |>.bind state.getVar
    let rhs ← op.operands[1]?.map (·.value) |>.bind state.getVar
    let result := { op := opPtr, index := 0 }
    let sum := lhs + rhs
    let newState ← state.setVar (ValuePtr.opResult result) sum
    return (newState, .Continue)
  | 3 => do -- return
    let results ← (0...op.results.size).toArray.mapM (fun i => do
      let resPtr : OpResultPtr := { op := opPtr, index := i }
      state.getVar (ValuePtr.opResult resPtr)
    )
    return (state, .Return results)
  | _ => none

def interpretOpList (ctx : IRContext) (opList : List OperationPtr) (hOpList : ∀ op, op ∈ opList → op.InBounds ctx) (state : InterpreterState) : Option (Array InterpreterValue) := do
  match opList with
  | [] => none
  | op :: opList =>
    let (newState, action) ← interpretOp ctx op (by grind) state
    match action with
    | .Continue => interpretOpList ctx opList (by grind) newState
    | .Return vals => return vals

theorem BlockPtr.operationListInBounds (block : BlockPtr) (ctx : IRContext) (hctx : ctx.WellFormed) (hblock : block.InBounds ctx) :
    ∀ op, op ∈ (block.operationList ctx hctx hblock) → op.InBounds ctx := by
  have : BlockPtr.OpChain block ctx (hctx.opChain block hblock).choose hblock := by
    apply BlockPtr.operationListWF; grind
  simp only [BlockPtr.operationList]
  intros op opInList
  grind [BlockPtr.OpChain, IRContext.WellFormed]

noncomputable def interpretBlock (ctx : IRContext) (blockPtr : BlockPtr) (inputs : Array InterpreterValue) (hblock : blockPtr.InBounds ctx := by grind) (hWF : ctx.WellFormed) : Option (Array UInt64) := do
  let block := blockPtr.get ctx (by grind)
  if block.arguments.size ≠ inputs.size then
    none
  else
    let initState ← ((0...block.arguments.size).toArray.zip inputs).foldlM (fun stateAcc (argIdx, inputState) => do
      let argPtr : BlockArgumentPtr := { block := blockPtr, index := argIdx }
      let argValuePtr : ValuePtr := ValuePtr.blockArgument argPtr
      let newState ← stateAcc.setVar argValuePtr inputState
      return newState
    ) InterpreterState.empty
    let opArray := blockPtr.operationList ctx hWF hblock
    interpretOpList ctx opArray.toList (by
      intros op opInList
      subst opArray
      apply BlockPtr.operationListInBounds
      · simp [BlockPtr.operationList] at *
        apply opInList
      · grind
      · grind
    ) initState
