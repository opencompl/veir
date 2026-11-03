// RUN: veir-opt %s -p=canonicalize | filecheck %s

// With no isolated or unregistered operation enclosing them, constants have no
// uniquing scope and are left alone.
"test.test"() ({
  "test.test"() ({
    %a = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%a) : (i32) -> ()
  }) : () -> ()
  %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "test.test"(%b) : (i32) -> ()
}) : () -> ()

// CHECK:       "test.test"() ({
// CHECK-NEXT:  ^{{[0-9]+}}():
// CHECK-NEXT:    "test.test"() ({
// CHECK-NEXT:    ^{{[0-9]+}}():
// CHECK-NEXT:      %[[A:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:      "test.test"(%[[A]]) : (i32) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:    %[[B:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:    "test.test"(%[[B]]) : (i32) -> ()
// CHECK-NEXT:  }) : () -> ()
