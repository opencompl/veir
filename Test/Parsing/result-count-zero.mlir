// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a:0 = "test.test"() : () -> ()
}) : () -> ()

// CHECK:result-count-zero.mlir:4:3: error: expected named operation to have at least 1 result
// CHECK-NEXT:  %a:0 = "test.test"() : () -> ()
// CHECK-NEXT:  ^
