// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `lshr (trunc (lshr x, C1)), C2` is `trunc (lshr x, (C1 + C2))`: the two logical
// right shifts compose at x's full width, then one trunc narrows the result.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i32}> ({
  ^bb0(%x: i64):
    %c1 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %inner = "llvm.lshr"(%x, %c1) : (i64, i64) -> i64
    %t = "llvm.trunc"(%inner) : (i64) -> i32
    %c2 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %r = "llvm.lshr"(%t, %c2) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the outer shift amount is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i64, i32) -> i32}> ({
  ^bb0(%x: i64, %s: i32):
    %c1 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %inner = "llvm.lshr"(%x, %c1) : (i64, i64) -> i64
    %t = "llvm.trunc"(%inner) : (i64) -> i32
    %r = "llvm.lshr"(%t, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The shifts fold to a single lshr by 5 + 3 = 8 at i64, then one trunc to i32.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[C:.*]] = "llvm.mlir.constant"() <{"value" = 8 : i64}> : () -> i64
// CHECK:      %[[L:.*]] = "llvm.lshr"(%[[X]], %[[C]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "llvm.trunc"(%[[L]]) : (i64) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant outer shift amount: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NS:.*]] : i32):
// CHECK:      %[[NT:.*]] = "llvm.trunc"(%{{.*}}) : (i64) -> i32
// CHECK:      %[[NR:.*]] = "llvm.lshr"(%[[NT]], %[[NS]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
