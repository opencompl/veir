import Veir.Input
import Veir.Passes.Mem2Reg.Basic

open Veir
open Veir.Input

private def operations (ctx : IRContext OpCode) (block : BlockPtr) : Array OperationPtr := Id.run do
  let mut result := #[]
  let mut next := block.getFirstOp! ctx
  while let some op := next do
    result := result.push op
    next := op.getNextOp! ctx
  return result

/-- Promote the first allocation, checking verification and the order of the
surviving operations. Return `none` if the candidate is rejected. -/
private def run (mlir : String) :
    Except String (Option (WfIRContext OpCode × BlockPtr)) := do
  let (ctx, root, _) ← parseSourceString mlir.toUTF8
  let region := root.getRegion! ctx.raw 0
  let some block := region.getFirstBlock! ctx.raw | throw "missing entry"
  let original := operations ctx.raw block
  let some allocation := original.find? (·.getOpType! ctx.raw == .llvm .alloca)
    | throw "missing allocation"
  let pointer : ValuePtr := allocation.getResult 0
  let retained := original.filter fun op =>
    if op = allocation then false else
    match op.getOpType! ctx.raw with
    | .llvm .load => op.getOperand! ctx.raw 0 != pointer
    | .llvm .store => op.getOperand! ctx.raw 1 != pointer
    | _ => true
  let some (changed, target) := Mem2Reg.promoteSingleBlock? ctx region allocation
    | throw "promotion failed"
  if !changed then
    unless operations target.raw block == original do
      throw "changed operations for a rejected candidate"
    return none
  target.verify root
  unless operations target.raw block == retained do
    throw "unexpected change to operation order"
  return some (target, block)

private def rejects (mlir : String) : Except String Bool := do
  return (← run mlir).isNone

private def returnedArgument (mlir : String) : Except String Nat := do
  let some (ctx, block) ← run mlir
    | throw "rejected a supported allocation"
  let some terminator := block.getLastOp! ctx.raw | throw "missing return"
  let .blockArgument argument := terminator.getOperand! ctx.raw 0
    | throw "return operand is not a block argument"
  unless argument.block == block do throw "returned an argument of another block"
  return argument.index

private def simple : String := r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard returnedArgument simple = .ok 0

#guard returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i16) -> i16}> ({
^entry(%a: i16):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i16}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i16, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i16
  "func.return"(%r) : (i16) -> ()
}) : () -> ()"# = .ok 0

#guard returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
^entry(%a: i32):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
  "func.return"(%r) : (i32) -> ()
}) : () -> ()"# = .ok 0

#guard returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i64) -> i64}> ({
^entry(%a: i64):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i64, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
  "func.return"(%r) : (i64) -> ()
}) : () -> ()"# = .ok 0

private def testLlvmCount : Except String Nat :=
  returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testLlvmCount = .ok 0

private def testLastStore : Except String Nat :=
  returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i8, i8) -> i8}> ({
^entry(%a: i8, %b: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "llvm.store"(%b, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testLastStore = .ok 1

/-- Loads on either side of a store have different reaching definitions.
The stored addition is preserved with both operands forwarded. -/
private def testStoredArithmetic : Except String Unit := do
  let some (ctx, block) ← run r#""func.func"() <{sym_name = "f", function_type = (i8, i8) -> i8}> ({
^entry(%a: i8, %b: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %left = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%b, %p) : (i8, !llvm.ptr) -> ()
  %right = "llvm.load"(%p) : (!llvm.ptr) -> i8
  %sum = "arith.addi"(%left, %right) : (i8, i8) -> i8
  "llvm.store"(%sum, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"# | throw "rejected a supported allocation"
  let some addition := (operations ctx.raw block).find? (·.getOpType! ctx.raw == .arith .addi)
    | throw "missing addition"
  let a : ValuePtr := block.getArgument 0
  let b : ValuePtr := block.getArgument 1
  unless addition.getOperands! ctx.raw == #[a, b] do
    throw "incorrect addition operands"
  let some terminator := block.getLastOp! ctx.raw | throw "missing return"
  unless terminator.getOperand! ctx.raw 0 == (addition.getResult 0 : ValuePtr) do
    throw "did not return the stored addition"

#guard testStoredArithmetic = .ok ()

private def testNonUnitCount : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %two = "arith.constant"() <{value = 2 : i64}> : () -> i64
  %p = "llvm.alloca"(%two) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testNonUnitCount = .ok true

private def testDynamicCount : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i64, i8) -> i8}> ({
^entry(%count: i64, %a: i8):
  %p = "llvm.alloca"(%count) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testDynamicCount = .ok true

private def testInalloca : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8, inalloca}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testInalloca = .ok true
#guard rejects r#""func.func"() <{sym_name = "f", function_type = (i128) -> i128}> ({
^entry(%a: i128):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i128}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i128, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i128
  "func.return"(%r) : (i128) -> ()
}) : () -> ()"# = .ok true

-- Unused allocations without an initialising store are left unchanged.
#guard rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "func.return"(%a) : (i8) -> ()
}) : () -> ()"# = .ok true

private def testVolatileLoad : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) <{volatile_}> : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testVolatileLoad = .ok true

private def testVolatileStore : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) <{volatile_}> : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testVolatileStore = .ok true

private def testLoadBeforeStore : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testLoadBeforeStore = .ok true

private def testMixedStoreType : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %wide = "arith.constant"() <{value = 3 : i16}> : () -> i16
  "llvm.store"(%wide, %p) : (i16, !llvm.ptr) -> ()
  "func.return"(%a) : (i8) -> ()
}) : () -> ()"#

#guard testMixedStoreType = .ok true

private def testMixedLoadType : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %wide = "llvm.load"(%p) : (!llvm.ptr) -> i16
  "func.return"(%a) : (i8) -> ()
}) : () -> ()"#

#guard testMixedLoadType = .ok true

private def testStoredPointer : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %q = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
  "llvm.store"(%p, %q) : (!llvm.ptr, !llvm.ptr) -> ()
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "func.return"(%a) : (i8) -> ()
}) : () -> ()"#

#guard testStoredPointer = .ok true

private def testPointerCast : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %address = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testPointerCast = .ok true

-- Forwarding the first load also changes the following store's operand.
private def testStoreOfLoad : Except String Nat :=
  returnedArgument r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %first = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%first, %p) : (i8, !llvm.ptr) -> ()
  %last = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%last) : (i8) -> ()
}) : () -> ()"#

#guard testStoreOfLoad = .ok 0

private def testMultipleBlocks : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "cf.br"() [^exit] : () -> ()
^exit:
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testMultipleBlocks = .ok true

-- Intrinsic calls have no ordinary call interface but must also be rejected.
private def testIntrinsicCall : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "llvm.call_intrinsic"() <{intrin = "llvm.donothing", op_bundle_sizes = array<i32>,
    operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testIntrinsicCall = .ok true

private def testNestedRegion : Except String Bool :=
  rejects r#""func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "builtin.module"() ({
    "test.test"() : () -> ()
  }) : () -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"#

#guard testNestedRegion = .ok true

/-- The other allocation and its accesses survive. Its final store uses an
addition whose first operand was a load from the promoted allocation. -/
private def testOtherAllocation : Except String Unit := do
  let some (ctx, block) ← run r#""func.func"() <{sym_name = "f", function_type = (i8, i8) -> i8}> ({
^entry(%a: i8, %b: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %q = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%b, %q) : (i8, !llvm.ptr) -> ()
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %other = "llvm.load"(%q) : (!llvm.ptr) -> i8
  %first = "llvm.load"(%p) : (!llvm.ptr) -> i8
  %sum = "arith.addi"(%first, %other) : (i8, i8) -> i8
  "llvm.store"(%sum, %q) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()"# | throw "rejected a supported allocation"
  let ops := operations ctx.raw block
  let some allocation := ops.find? (·.getOpType! ctx.raw == .llvm .alloca)
    | throw "removed the other allocation"
  let some load := ops.find? (·.getOpType! ctx.raw == .llvm .load)
    | throw "removed the other load"
  let some addition := ops.find? (·.getOpType! ctx.raw == .arith .addi)
    | throw "removed the addition"
  let pointer : ValuePtr := allocation.getResult 0
  let a : ValuePtr := block.getArgument 0
  let b : ValuePtr := block.getArgument 1
  let loaded : ValuePtr := load.getResult 0
  let sum : ValuePtr := addition.getResult 0
  unless load.getOperands! ctx.raw == #[pointer] &&
      addition.getOperands! ctx.raw == #[a, loaded] do
    throw "incorrect operands after forwarding"
  let stores := ops.filter (·.getOpType! ctx.raw == .llvm .store)
  unless stores.map (·.getOperands! ctx.raw) ==
      #[#[b, pointer], #[sum, pointer]] do
    throw "changed the other allocation's stores"
  let some terminator := block.getLastOp! ctx.raw | throw "missing return"
  unless terminator.getOperand! ctx.raw 0 == a do
    throw "returned the wrong reaching definition"

#guard testOtherAllocation = .ok ()
