module
import Veir.Passes.RegisterAllocation.RegisterStack
meta import Veir.Passes.RegisterAllocation.RegisterStack

import Veir.Passes.RegisterAllocation.RegisterAllocator
meta import Veir.Passes.RegisterAllocation.RegisterAllocator

open Veir

/-! Test RegisterStack -/

/- Fresh stack is empty -/
#guard (default : RegisterStack .int).free = []

/- Fresh stack starts at index 0 -/
#guard (default : RegisterStack .int).next = 0

/- First allocated registers have indices -1 and -2, stack remains empty -/
#guard Id.run do
  let (first, stack) := (default : RegisterStack .int).pop
  let (second, stack) := stack.pop
  return first.index == some (-1) && second.index == some (-2) &&
    stack.next == 2 && stack.free.isEmpty

/- Registers that are pushed on the stack are reused -/
#guard Id.run do
  let (first, stack) := (default : RegisterStack .int).pop
  let (second, stack) := stack.pop
  let stack := (stack.push (-1)).push (-2)
  let (reusedSecond, stack) := stack.pop
  let (reusedFirst, stack) := stack.pop
  let (fresh, stack) := stack.pop
  return reusedSecond == second && reusedFirst == first &&
    fresh.index == some (-3) && stack.next == 3 && stack.free.isEmpty

/- A stack hands out registers of its own class, both fresh and reused -/
#guard (default : RegisterStack .int).pop.1 == RegisterType.mk .int (some (-1))
#guard (default : RegisterStack .stack).pop.1 == RegisterType.mk .stack (some (-1))
#guard ((default : RegisterStack .stack).push (-4)).pop.1 == RegisterType.mk .stack (some (-4))

/-! Test RegisterAllocator functions -/

/-- Create a module with an empty block for allocation tests. -/
private def emptyBlock : WfIRContext OpCode × BlockPtr :=
  let (ctx, root) := WfIRContext.create! OpCode
  let block := ((root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  (ctx, block)

/-- Append a `test.test` operation with the given result types and operands to the block. -/
private def addTestOp (ctx : WfIRContext OpCode) (block : BlockPtr)
    (types : Array TypeAttr) (operands : Array ValuePtr := #[]) :
    WfIRContext OpCode × OperationPtr :=
  (WfRewriter.createOp! ctx Test.test types operands #[] #[] ()
    (some (.atEnd block))).get!

/--
Test `allocateRegister` on a single result, checking that repeated allocation preserves the
assignment and stack. Return the assigned register, updated result type, free registers, and
next fresh index.
-/
private def testAllocateRegister (type : TypeAttr) (stack : RegisterStack .int := default) :
    Except String (RegisterType × TypeAttr × List Int × Nat) := do
  let (ctx, block) := emptyBlock
  let (ctx, op) := addTestOp ctx block #[type]
  let value := op.getResult 0
  let (ctx, stack, reg) ← allocateRegister ctx value stack
  let (ctx, repeatedStack, repeatedReg) ← allocateRegister ctx value stack
  unless repeatedReg == reg && repeatedStack.free == stack.free &&
      repeatedStack.next == stack.next do
    throw "repeated allocation changed the assignment or stack"
  return (reg, value.getType! ctx.raw, stack.free, stack.next)

/- An unassigned register receives a fresh virtual register. -/
#guard testAllocateRegister RegisterType.mk =
  .ok (RegisterType.mk .int (some (-1)), RegisterType.mk .int (some (-1)), [], 1)

/- An unassigned register reuses a free register without advancing the fresh index. -/
#guard testAllocateRegister RegisterType.mk
    { free := [-4], next := 7 } =
  .ok (RegisterType.mk .int (some (-4)), RegisterType.mk .int (some (-4)), [], 7)

/- A physical register is preserved without consuming a free register. -/
#guard testAllocateRegister (RegisterType.mk .int (some 0))
    { free := [-4], next := 7 } =
  .ok (RegisterType.mk .int (some 0), RegisterType.mk .int (some 0), [-4], 7)

/- Register allocation rejects a value with a non-register type. -/
#guard testAllocateRegister (IntegerType.signless 32) =
  .error "expected a register-typed value"

/-- Collect register indices from SSA values, rejecting non-register types. -/
private def indices (ctx : WfIRContext OpCode) (values : Array ValuePtr) :
    Except String (Array (Option Int)) :=
  values.mapM fun value => do
    let .registerType reg := (value.getType! ctx.raw).val
      | throw "expected a register-typed value"
    return reg.index

/--
Test that `allocateBlock` preserves an empty block.

Expected program:
```mlir
"builtin.module"() ({
  ^2():
}) : () -> ()
```
-/
private def testEmptyBlock : Except String Bool := do
  let (ctx, block) := emptyBlock
  let (ctx, _) ← allocateBlock ctx block
  return (block.getFirstOp! ctx.raw).isNone && (block.getLastOp! ctx.raw).isNone

#guard testEmptyBlock = .ok true

/--
Test that a result can share a virtual register with an operand whose last use is this operation.

Expected program:
```mlir
"builtin.module"() ({
  ^2():
    %3 = "test.test"() : () -> !riscv.reg<j0>
    %4 = "test.test"() : () -> !riscv.reg<j1>
    %5 = "test.test"(%3, %4) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
}) : () -> ()
```
-/
private def testAllocateBlock : Except String (Array (Option Int)) := do
  let (ctx, block) := emptyBlock
  let (ctx, a) := addTestOp ctx block #[RegisterType.mk]
  let (ctx, b) := addTestOp ctx block #[RegisterType.mk]
  let (ctx, sum) := addTestOp ctx block #[RegisterType.mk]
    #[a.getResult 0, b.getResult 0]
  let (ctx, _) ← allocateBlock ctx block
  indices ctx #[a.getResult 0, b.getResult 0, sum.getResult 0]

#guard testAllocateBlock = .ok #[some (-1), some (-2), some (-1)]

/--
Test that repeated uses of the same operand share one register assignment.

Expected program:
```mlir
"builtin.module"() ({
  ^2():
    %3 = "test.test"() : () -> !riscv.reg<j0>
    %4 = "test.test"(%3, %3) : (!riscv.reg<j0>, !riscv.reg<j0>) -> !riscv.reg<j0>
}) : () -> ()
```
-/
private def testRepeatedOperand : Except String (Array (Option Int)) := do
  let (ctx, block) := emptyBlock
  let (ctx, a) := addTestOp ctx block #[RegisterType.mk]
  let (ctx, sum) := addTestOp ctx block #[RegisterType.mk]
    #[a.getResult 0, a.getResult 0]
  let (ctx, _) ← allocateBlock ctx block
  indices ctx #[a.getResult 0, sum.getResult 0]

#guard testRepeatedOperand = .ok #[some (-1), some (-1)]

/--
Test that unused results of the same operation receive distinct virtual registers.

Expected program:
```mlir
"builtin.module"() ({
  ^2():
    %3:2 = "test.test"() : () -> (!riscv.reg<j0>, !riscv.reg<j1>)
}) : () -> ()
```
-/
private def testUnusedResults : Except String (Array (Option Int)) := do
  let (ctx, block) := emptyBlock
  let (ctx, op) := addTestOp ctx block #[RegisterType.mk, RegisterType.mk]
  let (ctx, _) ← allocateBlock ctx block
  indices ctx (op.getResults! ctx.raw)

#guard testUnusedResults = .ok #[some (-1), some (-2)]

/--
Test that a physical register assignment is preserved and is not reused for unassigned values.

Expected program:
```mlir
"builtin.module"() ({
  ^2():
    %3 = "test.test"() : () -> !riscv.reg<j0>
    %4 = "test.test"() : () -> !riscv.reg<j1>
    %5 = "test.test"(%3, %4) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
    %6 = "test.test"() : () -> !riscv.reg<x0>
}) : () -> ()
```
-/
private def testPhysicalRegister : Except String (Array (Option Int)) := do
  let (ctx, block) := emptyBlock
  let (ctx, a) := addTestOp ctx block #[RegisterType.mk]
  let (ctx, b) := addTestOp ctx block #[RegisterType.mk]
  let (ctx, sum) := addTestOp ctx block #[RegisterType.mk]
    #[a.getResult 0, b.getResult 0]
  let (ctx, zero) := addTestOp ctx block #[RegisterType.mk .int (some 0)]
  let (ctx, _) ← allocateBlock ctx block
  indices ctx #[a.getResult 0, b.getResult 0, sum.getResult 0, zero.getResult 0]

#guard testPhysicalRegister = .ok #[some (-1), some (-2), some (-1), some 0]

/--
Test that `allocateBlock` rejects an operation with a non-register result.

Input program (allocation fails):
```mlir
"builtin.module"() ({
  ^2():
    %3 = "test.test"() : () -> i32
}) : () -> ()
```
-/
private def testNonRegisterBlock : Except String Unit := do
  let (ctx, block) := emptyBlock
  let (ctx, _) := addTestOp ctx block #[IntegerType.signless 32]
  let _ ← allocateBlock ctx block

#guard testNonRegisterBlock = .error "expected a register-typed value"
