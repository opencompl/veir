// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %1 = "test.test"() : () -> ((i32) -> (i32))
  %2 = "test.test"() : () -> ((i32) -> ((i32) -> i32))
  %3 = "test.test"() <{str = "hello world"}> : () -> i32
  %4 = "test.test"() <{empty = ""}> : () -> i32
  %5 = "test.test"() <{escaped = "line1\nline2\ttab"}> : () -> i32
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> ((i32) -> i32)
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> ((i32) -> ((i32) -> i32))
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT: }) : () -> ()
