// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `trunc (zext x)` that round-trips back to `x`'s type folds to `x`.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %z = "llvm.zext"(%x) : (i32) -> i64
    %t = "llvm.trunc"(%z) : (i64) -> i32
    "func.return"(%t) : (i32) -> ()
  }) : () -> ()

  // Negative case: the trunc target width doesn't match x's width (i32 -> i16).
  "func.func"() <{function_type = (i32) -> i16}> ({
  ^bb0(%x: i32):
    %z = "llvm.zext"(%x) : (i32) -> i64
    %t = "llvm.trunc"(%z) : (i64) -> i16
    "func.return"(%t) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// Round-trip: both casts vanish and x is returned.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32):
// CHECK-NOT:  "llvm.trunc"
// CHECK:      "func.return"(%[[X]]) : (i32) -> ()

// Non-round-trip: the casts remain.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32):
// CHECK:      %[[NZ:.*]] = "llvm.zext"(%[[NX]]) : (i32) -> i64
// CHECK:      %[[NT:.*]] = "llvm.trunc"(%[[NZ]]) : (i64) -> i16
// CHECK:      "func.return"(%[[NT]]) : (i16) -> ()
