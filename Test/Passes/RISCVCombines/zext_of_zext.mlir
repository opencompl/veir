// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `zext (zext x)` collapses to a single `zext x` to the outer width.

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i8):
    %z0 = "llvm.zext"(%x) : (i8) -> i32
    %z1 = "llvm.zext"(%z0) : (i32) -> i64
    "func.return"(%z1) : (i64) -> ()
  }) : () -> ()

  // Negative case: a single zext is left alone.
  "func.func"() <{function_type = (i8) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i8):
    %z = "llvm.zext"(%x) : (i8) -> i64
    "func.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The two zexts collapse to one from i8 straight to i64.
// CHECK:      ^{{.*}}(%[[X:.*]] : i8):
// CHECK:      %[[Z:.*]] = "llvm.zext"(%[[X]]) : (i8) -> i64
// CHECK-NOT:  "llvm.zext"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Single zext unchanged.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i8):
// CHECK:      %[[NZ:.*]] = "llvm.zext"(%[[NX]]) : (i8) -> i64
// CHECK:      "func.return"(%[[NZ]]) : (i64) -> ()
