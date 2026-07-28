module

public import Veir.Interfaces.SideEffectInterfaces
public import Veir.Interpreter.Basic

/-!
# Compile-time evaluation of operations

An operation whose operands are all known constants can be executed at
compile time by the interpreter, which already defines the semantics of
every operation. This file provides that capability: `foldEvaluate` runs
one operation on known operand values.

Computing results this way, instead of reimplementing each operation's
semantics in the optimizer, is what makes a client agree with the runtime
semantics by construction. The intended clients are constant folding and
optimistic data-flow analyses such as SCCP.

Which operations may be evaluated is not a question this file answers: an
operation may be executed at compile time exactly when it is free of memory
effects, which `Veir.isMemoryEffectFree` already decides.
-/

public section

namespace Veir

/--
  Evaluate an operation with the interpreter, given the runtime values of its
  operands. Returns the result values, `Interp.ub` if the operation triggers
  UB, and `none` if the operation must not be evaluated or the interpreter
  cannot evaluate it.

  Operations that are not free of memory effects are rejected: they are the
  ones for which the empty memory supplied here is not a faithful stand-in for
  the program's memory. A non-volatile load is the case to keep in mind, since
  `hasSideEffects` alone reports it as removable and would let it through.

  UB is reported as such rather than converted to a value. A client that wants
  UB to refine to poison is choosing a policy, and needs the result type to
  build the poison value, so that conversion belongs to the client.
-/
def foldEvaluate (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) := do
  if !isMemoryEffectFree opCode properties then none else
  let (results, _mem, action) ←
    interpretOp' opCode properties resultTypes operands #[] MemoryState.empty
  -- Terminators are already excluded above, since `hasSideEffects` reports
  -- them as effectful; this is a backstop against an operation that reports
  -- no effects and still asks to transfer control.
  if action.isSome then none
  else return results

end Veir
