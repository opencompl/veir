// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
    "unregistered.op_one"() : () -> ()
}) : () -> ()

// CHECK:unregistered_op_error.mlir:4:5: error: op 'unregistered.op_one' is not registered. Consider using --allow-unregistered-dialect.
// CHECK-NEXT:    "unregistered.op_one"() : () -> ()
// CHECK-NEXT:    ^
