// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

!int = i32
!int = i64
"builtin.module"() ({
^bb0:
}) : () -> ()

// CHECK:type-alias-redefinition.mlir:5:1: error: redefinition of type alias id 'int'
// CHECK-NEXT:!int = i64
// CHECK-NEXT:^
