// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `sext (sext x)` collapses to a single `sext x` to the outer width.

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> i64}> ({
  ^bb0(%x: i8):
    %s0 = "llvm.sext"(%x) : (i8) -> i32
    %s1 = "llvm.sext"(%s0) : (i32) -> i64
    "func.return"(%s1) : (i64) -> ()
  }) : () -> ()

  // Negative case: a single sext is left alone.
  "func.func"() <{function_type = (i8) -> i64}> ({
  ^bb0(%x: i8):
    %s = "llvm.sext"(%x) : (i8) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The two sexts collapse to one from i8 straight to i64.
// CHECK:      ^{{.*}}(%[[X:.*]] : i8):
// CHECK:      %[[S:.*]] = "llvm.sext"(%[[X]]) : (i8) -> i64
// CHECK-NOT:  "llvm.sext"
// CHECK:      "func.return"(%[[S]]) : (i64) -> ()

// Single sext unchanged.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i8):
// CHECK:      %[[NS:.*]] = "llvm.sext"(%[[NX]]) : (i8) -> i64
// CHECK:      "func.return"(%[[NS]]) : (i64) -> ()
