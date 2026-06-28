// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_AGREE

// MLIR's generic verifier requires any operation with block successors to
// terminate its parent block, even if the operation is not a registered
// terminator. Otherwise non-terminator ops can smuggle CFG edges that ordinary
// terminator-based analyses do not see.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    "test.test"() [^side] : () -> ()
    "func.return"() : () -> ()
  ^side:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operation with block successors must terminate its parent block
