// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

!my.int = i32
"builtin.module"() ({
^bb0:
}) : () -> ()

// CHECK:type-alias-reserved-name.mlir:4:1: error: type names with a '.' are reserved for dialect-defined names
// CHECK-NEXT:!my.int = i32
// CHECK-NEXT:^
