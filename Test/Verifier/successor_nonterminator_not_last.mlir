// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// MLIR's generic verifier requires any operation carrying block successors to be
// the last operation of its block, even when the operation is not a registered
// terminator

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
