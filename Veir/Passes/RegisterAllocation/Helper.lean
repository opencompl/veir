module

public import Veir.GlobalOpInfo
public import Veir.Interfaces.FunctionInterfaces

namespace Veir

/--
The number of function arguments passed in registers, `a0`–`a7`.
Functions with more arguments pass the rest on the stack, which the allocator does not
support yet.
-/
def maxRegisterArguments : Nat := 8

/--
The number of function results returned in registers, `a0` and `a1`. Larger results are
returned through memory, which the allocator does not support yet.
-/
def maxRegisterResults : Nat := 2

/-- The ABI registers `a<i>` (`x(10+i)`) that hold function arguments and return values. -/
def aRegister (i : Nat) : RegisterType := { cls := .int, index := some (10 + i) }

/--
The results of function `funcOp`. An `llvm.func` that returns nothing declares a single
`!llvm.void` result, which is not a value and is dropped here.
-/
def functionResultTypes {ctx : IRContext OpCode} {op : OperationPtr}
    (funcOp : FunctionOp ctx op) : Array Attribute :=
  match funcOp.getResultTypes with
  | #[.llvmVoidType _] => #[]
  | outputs => outputs

/--
Check the calling-convention limits of the function `funcOp`, which precolouring and allocation
share: no variadic arguments, at most `maxRegisterArguments` arguments, and at most
`maxRegisterResults` results.

With `requirePrecoloured`, also check that every argument `i` is already assigned its
calling-convention register `a<i>` (`x10`, `x11`, ...) in the signature, as
`register-precolouring-riscv64` does.
-/
def checkCallingConvention {ctx : IRContext OpCode} {op : OperationPtr}
    (funcOp : FunctionOp ctx op) (requirePrecoloured : Bool := false) : Except String Unit := do
  if funcOp.getFunctionType.isVarArg then
    throw "register allocation does not support variadic functions"
  if funcOp.getNumArguments > maxRegisterArguments then
    throw s!"register allocation supports at most {maxRegisterArguments} function arguments"
  if (functionResultTypes funcOp).size > maxRegisterResults then
    throw s!"register allocation supports at most {maxRegisterResults} function results"
  if requirePrecoloured then
    for (t, i) in funcOp.getArgumentTypes.zipIdx do
      if t != .registerType (aRegister i) then
        throw s!"register allocation requires argument {i} to be precoloured to {aRegister i}; \
          run register-precolouring-riscv64 first"

/--
Return block from module op, while enforcing the allocator's current restrictions on structures we can handle.

We accept only operations with:
- exactly one region
- this region has either one or zero blocks
- if it has a block, the block has no arguments
Invalid input throws an error.

Return the block inside `op`, or `none` if its region is empty.
-/
def getModuleBlock (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Option BlockPtr) := do
  if op.getNumRegions! ctx.raw != 1 then
    throw "register allocation expects a module with a single region"
  let region := (op.getRegions! ctx.raw)[0]!
  let some block := region.getFirstBlock! ctx.raw | return none
  if (block.getNextBlock! ctx.raw).isSome then
    throw "register allocation expects a module body with a single block"
  if block.getNumArguments! ctx.raw != 0 then
    throw "register allocation does not support block arguments"
  return some block

/--
Return block from function op, while enforcing the allocator's current restrictions.

We accept only functions with:
- the calling-convention limits of `checkCallingConvention`, with precoloured arguments
- one or zero blocks
- if it has a block, the block has no nested regions
- if it has a block, the block has no calls. Otherwise, a value live across a call could be
  given a caller-saved register.
Invalid input throws an error.

Return the block inside function `f`, or `none` if it has no block.
-/
def getFunctionEntry (ctx : WfIRContext OpCode) (f : OperationPtr) :
    Except String (Option BlockPtr) := do
  let some funcOp := FunctionOp.of? f ctx.raw | return none
  let some entry := funcOp.getEntryBlock? | return none
  if (entry.getNextBlock! ctx.raw).isSome then
    throw "register allocation requires a single-block function"
  checkCallingConvention funcOp (requirePrecoloured := true)
  let mut inner? := entry.getFirstOp! ctx.raw
  -- scan for nested regions and calls inside each operation
  while let some inner := inner? do
      inner? := inner.getNextOp! ctx.raw
      if inner.getNumRegions! ctx.raw != 0 then
          throw "register allocation does not support operations with nested regions"
      if inner.getOpType! ctx.raw == .riscv_cf .call then
          throw "register allocation does not support function calls"
  return some entry

/--
The entry block of the function `f`, or `none` if `f` is not a function or has no body.
-/
def functionEntry? (ctx : WfIRContext OpCode) (f : OperationPtr) : Option BlockPtr :=
  (FunctionOp.of? f ctx.raw).bind (·.getEntryBlock?)

/--
The functions in the module `op` that have a body, or an error naming the first constraint
`op` breaks.

The shape of module this accepts, from the outside in:

- a *single region*, holding
- a *single block*, the module body, with *no block arguments*, holding
- *sibling functions*, each accepted by `getFunctionEntry`.

Anything else is rejected rather than worked around.

Operations in the module body that are not function are passed over, as are function
declarations, which have no body to allocate.
-/
def allocatableFunctions (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Array OperationPtr) := do
    let some block ← getModuleBlock ctx op | return #[]
    let mut funcs : Array OperationPtr := #[]
    let mut f? := block.getFirstOp! ctx.raw
    while let some f := f? do
        f? := f.getNextOp! ctx.raw
        let some _ ← getFunctionEntry ctx f | continue
        funcs := funcs.push f
    return funcs


end Veir
