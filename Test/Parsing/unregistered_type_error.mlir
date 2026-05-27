// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
    "func.return"() : () -> !bar.baz
}) : () -> ()

// CHECK:unregistered_type_error.mlir:4:29: error: type is not registered. Consider using --allow-unregistered-dialect.
// CHECK-NEXT:    "func.return"() : () -> !bar.baz
// CHECK-NEXT:                            ^
