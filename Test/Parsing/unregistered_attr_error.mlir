// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
    "func.return"() {foo = #bar<baz>} : () -> ()
}) : () -> ()

// CHECK:unregistered_attr_error.mlir:5:28: error: attribute '#bar' is not registered. Consider using --allow-unregistered-dialect.
// CHECK-NEXT:    "func.return"() {foo = #bar<baz>} : () -> (
// CHECK-NEXT:                           ^
