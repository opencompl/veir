// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
    "func.return"() : () -> !int
}) : () -> ()

// CHECK:type-alias-undefined.mlir:5:29: error: undefined symbol alias id 'int'
// CHECK-NEXT:    "func.return"() : () -> !int
// CHECK-NEXT:                            ^
