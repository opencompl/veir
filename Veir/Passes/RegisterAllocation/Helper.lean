module

public import Veir.GlobalOpInfo
import Veir.Interfaces.FunctionInterfaces

namespace Veir

public section

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
end

end Veir
