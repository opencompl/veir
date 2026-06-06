// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{sym_name = "f", visibility = "private", function_type = (i32) -> i32}> ({
  ^bb0(%arg0: i32):
    "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{
// CHECK-SAME:   "sym_name" = "f"
// CHECK-SAME:   "visibility" = "private"
// CHECK-SAME: }> ({
