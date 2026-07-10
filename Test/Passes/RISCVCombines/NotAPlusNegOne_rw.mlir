// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `not (X + -1)` is `-X`: since `~(X - 1) == -X`, it rewrites to `sub 0, X`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %add = "llvm.add"(%x, %m1) : (i64, i64) -> i64
    %r = "llvm.xor"(%add, %m1) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the added constant is -2, not -1, so the identity fails.
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %m2 = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    %add = "llvm.add"(%x, %m2) : (i64, i64) -> i64
    %r = "llvm.xor"(%add, %m1) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to 0 - X.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK:      %[[R:.*]] = "llvm.sub"(%[[Z]], %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Added constant is not -1: the not/add survive.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NX]],
// CHECK:      %[[NR:.*]] = "llvm.xor"(%[[NADD]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
