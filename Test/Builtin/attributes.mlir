// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %3 = "test.test"() <{str = "hello world"}> : () -> i32
  %4 = "test.test"() <{empty = ""}> : () -> i32
  %5 = "test.test"() <{escaped = "line1\nline2\ttab"}> : () -> i32
  %6 = "test.test"() <{unregistered = #unregistered.dialect<foo 3 + 2>}> : () -> i32
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> i32
// CHECK-NEXT: }) : () -> ()
