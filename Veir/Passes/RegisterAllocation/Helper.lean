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
- at most `maxRegisterArguments` arguments, all passed in registers
- at most `maxRegisterResults` results
- no variadic arguments i.e. (riscv.reg, ...)
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
  if funcOp.getFunctionType.isVarArg then
    throw "register allocation does not support variadic functions"
  if entry.getNumArguments! ctx.raw > maxRegisterArguments then
    throw s!"register allocation supports at most {maxRegisterArguments} function arguments"
  if (functionResultTypes funcOp).size > maxRegisterResults then
    throw s!"register allocation supports at most {maxRegisterResults} function results"
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
Check that every argument of the entry block `entry` is already assigned a physical register,
as `register-precolouring-riscv64` does. The allocator would otherwise give an argument a
virtual register, which the function signature does not mention, and which no calling
convention can pass.
-/
def checkPrecolouredArguments (ctx : WfIRContext OpCode) (entry : BlockPtr) :
    Except String Unit := do
  for i in [0:entry.getNumArguments! ctx.raw] do
    let arg : ValuePtr := .blockArgument { block := entry, index := i }
    match (arg.getType! ctx.raw).val with
    | .registerType { index := some n, .. } => if n < 0 then
        throw "register allocation requires precoloured function arguments; run register-precolouring-riscv64 first"
    | _ =>
        throw "register allocation requires precoloured function arguments; run register-precolouring-riscv64 first"

/--
The entry blocks of the functions in the module `op`, or an error naming the first
constraint `op` breaks.

The shape of module this accepts, from the outside in:

- a *single region*, holding
- a *single block*, the module body, with *no block arguments*, holding
- *sibling functions*, each accepted by `getFunctionEntry`.

Anything else is rejected rather than worked around.

Operations in the module body that are not function are passed over, as are function
declarations, which have no body to allocate.
-/
def allocatableBlocks (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Array BlockPtr) := do
    let some block ← getModuleBlock ctx op | return #[]
    let mut entries : Array BlockPtr := #[]
    let mut f? := block.getFirstOp! ctx.raw
    while let some f := f? do
        f? := f.getNextOp! ctx.raw
        let some fctBlock ← getFunctionEntry ctx f | continue
        entries := entries.push fctBlock
    return entries


end Veir
