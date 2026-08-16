// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A nested builtin.module establishes a fresh isolated scope.

"builtin.module"() ({
  %v = "arith.constant"() <{value = 0 : i32}> : () -> i32
  "builtin.module"() ({
    "test.test"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand uses a value defined outside the isolated region
