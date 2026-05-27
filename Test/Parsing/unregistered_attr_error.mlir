// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
    "func.return"() {foo = #bar<baz>} : () -> ()
}) : () -> ()

// CHECK:unregistered_attr_error.mlir:4:28: error: attribute is not registered. Consider using --allow-unregistered-dialect.
// CHECK-NEXT:    "func.return"() {foo = #bar<baz>} : () -> (
// CHECK-NEXT:                           ^
