// RUN: not veir-opt %s 2>&1 | filecheck %s

// Only a block that is alone in its region may go without a terminator (and
// only under an operation with unknown or terminator-free semantics, like the
// test dialect here). In a multi-block region every block must be non-empty
// and end in a possible terminator, mirroring MLIR's mayBeValidWithoutTerminator
// (mlir/lib/IR/Verifier.cpp). mlir-opt rejects this program the same way
// ("empty block: expect at least a terminator"); we cannot assert that with
// MLIR_INVALID because mlir-opt already rejects the unregistered test ops
// without --allow-unregistered-dialect.

"builtin.module"() ({
  "test.test"() ({
  ^bb0():
    "test.test"() : () -> ()
  ^bb1():
  }) : () -> ()
}) : () -> ()

// CHECK: Expected the block to end in a terminator, but the block is empty
