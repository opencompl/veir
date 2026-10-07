// RUN: veir-opt %s --allow-unregistered-dialect -p=canonicalize | filecheck %s

// An unregistered operation may be isolated from above, so each of its regions
// is a uniquing scope: constants are hoisted to the top of it but never out of
// it. Registered, non-isolated operations such as `test.test` are not scopes.
"foo.outer"() ({
  "test.test"() ({
    %a = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%a) : (i32) -> ()
  }) : () -> ()
  "foo.inner"() ({
    "test.test"() : () -> ()
    %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%b) : (i32) -> ()
  }) : () -> ()
  %c = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "test.test"(%c) : (i32) -> ()
}) : () -> ()

// CHECK:       "foo.outer"() ({
// CHECK-NEXT:  ^{{[0-9]+}}():
// CHECK-NEXT:    %[[C:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:    "test.test"() ({
// CHECK-NEXT:    ^{{[0-9]+}}():
// CHECK-NEXT:      "test.test"(%[[C]]) : (i32) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:    "foo.inner"() ({
// CHECK-NEXT:    ^{{[0-9]+}}():
// CHECK-NEXT:      %[[INNER:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:      "test.test"() : () -> ()
// CHECK-NEXT:      "test.test"(%[[INNER]]) : (i32) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:    "test.test"(%[[C]]) : (i32) -> ()
// CHECK-NEXT:  }) : () -> ()
