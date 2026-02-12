// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %5 = "test.test"() : () -> ((i32) -> (i32))
  %5 = "test.test"() : () -> ((i32) -> ((i32) -> i32))
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %5 = "test.test"() : () -> ((i32) -> i32)
// CHECK-NEXT:     %6 = "test.test"() : () -> ((i32) -> ((i32) -> i32))
// CHECK-NEXT: }) : () -> ()
