// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_UNREGISTERED_INVALID

"builtin.module"() ({
    "func.return"() {foo = #bar.baz : } : () -> ()
}) : () -> ()

// CHECK:unregistered_typed_attr_error.mlir:5:39: error: type expected
// CHECK-NEXT:    "func.return"() {foo = #bar.baz : } : () -> ()
// CHECK-NEXT:                                      ^
