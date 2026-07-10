// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
    %1 = "llvm.mlir.constant"() <{value = dense<0> : tensor<4xi8>}> : () -> !llvm.array<4 x i8>
    // CHECK: "llvm.mlir.constant"() <{"value" = dense<0> : tensor<4xi8>}> : () -> !llvm.array<4 x i8>
}) : () -> ()

