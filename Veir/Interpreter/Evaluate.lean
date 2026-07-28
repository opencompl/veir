module

public import Veir.Interpreter.Basic

/-!
# Compile-time evaluation of operations

An operation whose operands are all known constants can be executed at
compile time by the interpreter, which already defines the semantics of
every operation. This file provides that capability: `foldEvaluate` runs
one operation on known operand values, and `OpCode.isFoldEvaluable` says
which opcodes it may be used on.

Computing results this way, instead of reimplementing each operation's
semantics in the optimizer, is what makes a client agree with the runtime
semantics by construction. The intended clients are constant folding and
optimistic data-flow analyses such as SCCP.
-/

public section

namespace Veir

/--
  Opcodes whose interpretation may be evaluated at fold time: they must be
  pure, memory-independent, and free of control flow.

  Note: this is deliberately not `OpCode.hasSideEffects`, which classifies
  non-volatile `llvm.load` as non-side-effecting. Evaluating a load at fold
  time would read from a dummy memory and miscompile.
-/
def OpCode.isFoldEvaluable : OpCode → Bool
  | .arith _ => true
  | .llvm op => match op with
    | .add | .sub | .mul | .sdiv | .udiv | .srem | .urem
    | .shl | .lshr | .ashr | .and | .or | .xor => true
    | _ => false
  | .riscv op => match op with
    -- Loads and stores must not be evaluated at fold time (note that loads
    -- read memory even though `hasSideEffects` classifies them as pure).
    | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu
    | .sd | .sw | .sh | .sb => false
    -- Everything else is pure register arithmetic.
    | _ => true
  | _ => false

/--
  Evaluate a side-effect-free operation with the interpreter. Returns the
  result values, `Interp.ub` if the operation triggers UB, and `none` if the
  interpreter cannot evaluate it (or it performs control flow).

  Must only be called for `isFoldEvaluable` opcodes: those neither read nor
  write memory, so the dummy memory state is irrelevant.
-/
def foldEvaluate (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) := do
  let (results, _mem, action) ←
    interpretOp' opCode properties resultTypes operands #[] MemoryState.empty
  if action.isSome then none
  else return results

end Veir
