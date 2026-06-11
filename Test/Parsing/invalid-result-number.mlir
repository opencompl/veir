// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a = "test.test"() : () -> i32
  %b = "test.test"(%a#abc) : (i32) -> i1
}) : () -> ()

// CHECK:invalid-result-number.mlir:5:22: error: invalid SSA value result number
// CHECK-NEXT:  %b = "test.test"(%a#abc) : (i32) -> i1
// CHECK-NEXT:                     ^
