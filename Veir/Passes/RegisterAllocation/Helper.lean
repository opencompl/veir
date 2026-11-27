module

public import Veir.GlobalOpInfo
import Veir.Interfaces.FunctionInterfaces

namespace Veir

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
- no arguments (TODO: will be added soon)
- no return values (TODO: will be added soon)
- this one or zero blocks
- if it has a block, the block has no arguments
- if it has a block, the block has no nested regions
Invalid input throws an error.

Return the block inside function `f`, or `none` if it has no block.
-/
def getFunctionEntry (ctx : WfIRContext OpCode) (f : OperationPtr) :
    Except String (Option BlockPtr) := do
  let some funcOp := FunctionOp.of? f ctx.raw | return none
  let some entry := funcOp.getEntryBlock? | return none
  if (entry.getNextBlock! ctx.raw).isSome then
    throw "register allocation requires a single-block function"
  -- TODO: Functions cannot take arguments yet, which is not very useful. Will be changed soon.
  if entry.getNumArguments! ctx.raw != 0 then
    throw "register allocation does not support block arguments"
  let mut inner? := entry.getFirstOp! ctx.raw
  -- scan for nested regions inside each operation
  while let some inner := inner? do
      inner? := inner.getNextOp! ctx.raw
      if inner.getNumRegions! ctx.raw != 0 then
          throw "register allocation does not support operations with nested regions"
  if funcOp.getNumResults != 0 then
    throw "register allocation does not support function return values"
  return some entry



/--
The entry blocks of the functions in the module `op`, or an error naming the first
constraint `op` breaks.

The shape of module this accepts, from the outside in:

- a *single region*, holding
- a *single block*, the module body, with *no block arguments*, holding
- *sibling functions*, each with *no input arguments* and *no return values*, whose body is
  a *single block* with *no nested regions* in it.

Anything else is rejected rather than worked around.

Operations in the module body that are not function are passed over, as are function
declarations, which have no body to allocate.
-/

public def allocatableBlocks (ctx : WfIRContext OpCode) (op : OperationPtr) :
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
