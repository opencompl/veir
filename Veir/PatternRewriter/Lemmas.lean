import Veir.PatternRewriter.Basic
import Veir.Interpreter

namespace Veir.PatternRewriter

def interpretOpArray (ctx : IRContext) (array : Array OperationPtr) (state : InterpreterState)
    (index : Nat := 0)
    (opInBounds : ∀ op ∈ array, op.InBounds ctx := by grind)
    (indexInBounds : index < array.size := by grind)
    : Option InterpreterState := do
  let (state, action) ← interpretOp ctx array[index] state
  match action with
  | .continue =>
    let next := index + 1
    if h: next < array.size then
      interpretOpArray ctx array state (index + 1)
    else
      return state
  | .return results =>
    return state

def LocalRewritePattern.PreservesSemantics (pattern : LocalRewritePattern) : Prop :=
  ∀ (ctx : IRContext) (op : OperationPtr) (opIn : op.InBounds ctx) newCtx newOps newValue,
    pattern ctx op = some (newCtx, some (newOps, #[newValue])) →
    ∀ state newState, interpretOp ctx op state = some (newState, .continue) →
    ∃ newState', interpretOpArray ctx newOps state 0 (by sorry) (by sorry) = some newState' ∧
    newState'.variables[newValue]! = newState.variables[ValuePtr.opResult (op.getResult 0)]!
