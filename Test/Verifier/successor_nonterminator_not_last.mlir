// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s

// MLIR's generic verifier requires any operation carrying block successors to be
// the last operation of its block, even when the operation is not a registered
// terminator (`verifyOnEntrance(Block &)` in mlir/lib/IR/Verifier.cpp):
//
//     // Only the last instructions is allowed to have successors.
//     if (op.getNumSuccessors() != 0 && &op != &block.back())
//
// Otherwise a non-terminator can smuggle a CFG edge into the middle of a block,
// where terminator-based analyses would not see it. mlir-opt rejects this program
// with the same message; we cannot assert that with MLIR_INVALID, because that
// substitution runs mlir-opt without --allow-unregistered-dialect, so it would
// fail on the unregistered op instead and pass vacuously.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    "test.sneaky_branch"() [^side] : () -> ()
    "func.return"() : () -> ()
  ^side:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operation with block successors must terminate its parent block
