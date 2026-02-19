import Veir.PatternRewriter.Basic
import Veir.Interpreter

namespace Veir.PatternRewriter

def interpretOpList' (ctx : IRContext) (list : List OperationPtr) (state : InterpreterState)
    (opInBounds : ∀ op ∈ list, op.InBounds ctx := by grind)
    : Option InterpreterState := do
  match list with
  | [] => return state
  | op :: rest =>
    let (state, action) ← interpretOp ctx op state
    match action with
    | .continue => interpretOpList' ctx rest state
    | .return results => none

def LocalRewritePattern.PreservesSemantics (pattern : LocalRewritePattern) : Prop :=
  ∀ (ctx : IRContext) (op : OperationPtr) (opIn : op.InBounds ctx) newCtx newOps newValue,
    pattern ctx op = some (newCtx, some (newOps, #[newValue])) →
    ∀ state newState, interpretOp ctx op state = some (newState, .continue) →
    ∃ newState', interpretOpList' ctx newOps.toList state (by sorry) = some newState' ∧
    newState'.variables[newValue]! = newState.variables[ValuePtr.opResult (op.getResult 0)]!
