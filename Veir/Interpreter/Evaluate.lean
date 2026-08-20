module

public import Veir.Interpreter.Basic

/-!
# Compile-time evaluation of operations
-/

public section

namespace Veir

/--
  Whether an operation is a candidate for evaluation by `foldEvaluate`.

  Evaluation runs the operation against memory that is not the program's, so
  it must have no memory effects at all.
-/
private def isFoldEvaluationCandidate
    (opCode : OpCode) (properties : propertiesOf opCode) : Bool :=
  HasOpInfo.getEffects opCode properties == .none

/--
  Evaluate an operation with the interpreter, given the runtime values of its
  operands. Returns the result values, `Interp.ub` if the operation triggers
  UB, and `Interp.fail` if the operation must not be evaluated or the interpreter
  cannot evaluate it.
-/
def foldEvaluate (opCode : OpCode) (properties : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) := do
  if !isFoldEvaluationCandidate opCode properties then none else
  let (results, _mem, action) ←
    interpretOp' opCode properties resultTypes operands #[] MemoryState.empty
  if action.isSome then none
  else return results

end Veir
