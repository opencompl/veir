// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Each module is its own uniquing scope. Each use must keep a local definition.
"builtin.module"() ({
  "builtin.module"() ({
    %a = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%a) : (i32) -> ()
  }) : () -> ()
  %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "test.test"(%b) : (i32) -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:  ^{{[0-9]+}}():
// CHECK-NEXT:    %[[OUTER:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:    "builtin.module"() ({
// CHECK-NEXT:    ^{{[0-9]+}}():
// CHECK-NEXT:      %[[INNER:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:      "test.test"(%[[INNER]]) : (i32) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:    "test.test"(%[[OUTER]]) : (i32) -> ()
// CHECK-NEXT:  }) : () -> ()
