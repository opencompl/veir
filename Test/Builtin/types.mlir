// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %0 = "test.test"() : () -> i32
  %1 = "test.test"() : () -> ((i32) -> (i32))
  %2 = "test.test"() : () -> ((i32) -> ((i32) -> i32))
  %3 = "test.test"() : () -> !unregistered.dialect<foo 3 + 2 - 4>
  %4 = "test.test"() : () -> !mod_arith.int<17 : i32>
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> ((i32) -> i32)
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> ((i32) -> ((i32) -> i32))
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !unregistered.dialect<foo 3 + 2 - 4>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !mod_arith.int<17 : i32>
// CHECK-NEXT: }) : () -> ()
