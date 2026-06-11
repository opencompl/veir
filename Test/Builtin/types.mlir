// RUN: VEIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "test.test"() : () -> i32
      %1 = "test.test"() : () -> ((i32) -> (i32))
      %2 = "test.test"() : () -> ((i32) -> ((i32) -> i32))
      %3 = "test.test"() : () -> !unregistered.dialect<foo 3 + 2 - 4>
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> ((i32) -> i32)
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> ((i32) -> ((i32) -> i32))
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> !unregistered.dialect<foo 3 + 2 - 4>
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
