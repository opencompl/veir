// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a:2 = "test.test"() : () -> (i32, i64)
  %b = "test.test"(%a#2) : (i32) -> i1
}) : () -> ()

// CHECK:invalid-result-index.mlir:5:20: error: invalid result index 2 for %a
// CHECK-NEXT:  %b = "test.test"(%a#2) : (i32) -> i1
// CHECK-NEXT:                   ^
// CHECK-NEXT:invalid-result-index.mlir:4:3: note: value defined here
// CHECK-NEXT:  %a:2 = "test.test"() : () -> (i32, i64)
// CHECK-NEXT:  ^
