// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `mul x, 2` becomes `add x, x`; the constant 2 must match exactly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %r = "llvm.mul"(%x, %c2) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: multiplying by 3 does not fold to a self-add.
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %r = "llvm.mul"(%x, %c3) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// mul-by-2 rewritten to x + x.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[R:.*]] = "llvm.add"(%[[X]], %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// mul-by-3 is left as a mul.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.mul"(%[[NX]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
