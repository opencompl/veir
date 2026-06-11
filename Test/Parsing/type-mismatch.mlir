// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a:2 = "test.test"() : () -> (i32, i64)
  %b = "test.test"(%a#1) : (i32) -> i1
}) : () -> ()

// CHECK:type-mismatch.mlir:5:20: error: type mismatch for value %a#1: expected i32, got i64
// CHECK-NEXT:  %b = "test.test"(%a#1) : (i32) -> i1
// CHECK-NEXT:                   ^
// CHECK-NEXT:type-mismatch.mlir:4:3: note: value defined here
// CHECK-NEXT:  %a:2 = "test.test"() : () -> (i32, i64)
// CHECK-NEXT:  ^
