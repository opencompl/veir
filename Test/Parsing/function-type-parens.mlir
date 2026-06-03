// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// A function type with a parenthesized input list parses, matching MLIR. See #675.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
    ^bb0(%arg0: i32):
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (i32) -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
