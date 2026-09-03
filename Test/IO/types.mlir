// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = (!io.address) -> (), sym_name = "main"}> ({
    ^bb0(%arg0: !io.address):
      %0 = "test.test"() : () -> !io.address
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (!io.address) -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : !io.address):
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> !io.address
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
