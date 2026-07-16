// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"()  <{function_type = (i32) -> i32, sym_name="foo"}> ({
      ^6(%arg6_0 : i32):
        "func.return"(%arg6_0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "func.func"() <{"function_type" = (i32) -> i32, "sym_name" = "foo"}> ({
// CHECK-NEXT:       ^6(%arg6_0 : i32):
// CHECK-NEXT:         "func.return"(%arg6_0) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
