// RUN: veir-opt %s -p=canonicalize | filecheck %s

// With no `IsolatedFromAbove` operation enclosing the constants, the top-level
// operation's region is the uniquing scope, as in MLIR's `getInsertionRegion`.
"test.test"() ({
  "test.test"() ({
    %one_a = "arith.constant"() <{value = 7 : i32}> : () -> i32
    "test.test"(%one_a) : (i32) -> ()
  }) : () -> ()
  %one_b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "test.test"(%one_b) : (i32) -> ()
}) : () -> ()

// CHECK:       "test.test"() ({
// CHECK-NEXT:  ^{{[0-9]+}}():
// CHECK-NEXT:    %[[C:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:    "test.test"() ({
// CHECK-NEXT:    ^{{[0-9]+}}():
// CHECK-NEXT:      "test.test"(%[[C]]) : (i32) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:    "test.test"(%[[C]]) : (i32) -> ()
// CHECK-NEXT:  }) : () -> ()
