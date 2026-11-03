module

public import Veir.IR.Attribute
public import Veir.Passes.RegisterAllocation.RegisterStack
public import Veir.Rewriter.WfRewriter
public import Veir.GlobalOpInfo

namespace Veir

public section
/--
Assign a register to an unassigned register-typed SSA value, updating its type in the context.
Preserve existing assignments and reject values with non-register types.
-/
def allocateRegister (ctx : WfIRContext OpCode) (value : ValuePtr) (stack : RegisterStack) :
    Except String (WfIRContext OpCode × RegisterStack × RegisterType) := do
  let .registerType reg := (value.getType! ctx.raw).val
    | throw "expected a register-typed value"
  if reg.index.isSome then return (ctx, stack, reg)
  let (reg, s) := stack.pop
  let ctx := WfRewriter.setType! ctx value reg
  return (ctx, s, reg)

/--
Allocate registers for an operation and all preceding operations in the same block by traversing backward.
For each operation, allocate registers for all unallocated results before releasing reusable registers.
At this stage, register reuse is limited to virtual registers.
Termination is guaranteed by the finite number of operations in the block.
-/
partial def allocateOps (ctx: WfIRContext OpCode) (op: Option OperationPtr) (stack: RegisterStack) :
    Except String (WfIRContext OpCode × RegisterStack) := do
    let some op := op | return (ctx, stack)
    let mut ctx := ctx
    let mut stack := stack
    let mut resultRegs : Array RegisterType := #[]

    for result in op.getResults! ctx.raw do
        let (newCtx, newStack, reg) ← allocateRegister ctx result stack
        ctx := newCtx
        stack := newStack
        resultRegs := resultRegs.push reg

    for reg in resultRegs do
        if reg.index.any (· < 0) then
            stack := stack.push reg

    for operand in op.getOperands! ctx.raw do
        let (newCtx, newStack, _) ← allocateRegister ctx operand stack
        ctx := newCtx
        stack := newStack

    allocateOps ctx (op.getPrevOp! ctx.raw) stack

/--
Allocate registers for all operations in a block, traversing backwards with the default empty register stack.
Return the context with updated register types on SSA values.
-/
def allocateBlock (ctx : WfIRContext OpCode) (block : BlockPtr) :
    Except String (WfIRContext OpCode) := do
  let (ctx, _) ← allocateOps ctx (block.getLastOp! ctx.raw) default
  return ctx
end
end Veir
