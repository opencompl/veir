// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `trunc (zext x)` that round-trips back to `x`'s type folds to `x`.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %z = "gmir.g_zext"(%x) : (i32) -> i64
    %t = "gmir.g_trunc"(%z) : (i64) -> i32
    "func.return"(%t) : (i32) -> ()
  }) : () -> ()

  // Negative case: the trunc target width doesn't match x's width (i32 -> i16).
  "func.func"() <{function_type = (i32) -> i16, sym_name = "bar"}> ({
  ^bb0(%x: i32):
    %z = "gmir.g_zext"(%x) : (i32) -> i64
    %t = "gmir.g_trunc"(%z) : (i64) -> i16
    "func.return"(%t) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// Round-trip: both casts vanish and x is returned.
// CHECK:      func.func @foo(%[[X:.*]]: i32) -> i32 {
// CHECK-NOT:  "gmir.g_trunc"
// CHECK:      "func.return"(%[[X]]) : (i32) -> ()

// Non-round-trip: the casts remain.
// CHECK:      func.func @bar(%[[NX:.*]]: i32) -> i16 {
// CHECK:      %[[NZ:.*]] = "gmir.g_zext"(%[[NX]]) : (i32) -> i64
// CHECK:      %[[NT:.*]] = "gmir.g_trunc"(%[[NZ]]) : (i64) -> i16
// CHECK:      "func.return"(%[[NT]]) : (i16) -> ()
