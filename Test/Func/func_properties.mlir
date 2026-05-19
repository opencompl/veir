// RUN: veir-opt %s | filecheck %s
//
// Lossless round-trip of a `func.func` carrying both the modelled `sym_name`
// property and an unmodelled property preserved via `extra`.

"builtin.module"() ({
  "func.func"() <{sym_name = "f", visibility = "private"}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{
// CHECK-SAME:   "sym_name" = "f"
// CHECK-SAME:   "visibility" = "private"
// CHECK-SAME: }> ({
