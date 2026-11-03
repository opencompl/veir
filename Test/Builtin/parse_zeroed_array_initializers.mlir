// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
    %1 = "llvm.mlir.constant"() <{value = dense<0> : tensor<4xi8>}> : () -> !llvm.array<4 x i8>
    // CHECK: "llvm.mlir.constant"() <{"value" = dense<0> : tensor<4xi8>}> : () -> !llvm.array<4 x i8>
    %2 = "llvm.mlir.constant"() <{value = dense<[32, 64]> : vector<2xi64>}> : () -> !llvm.array<2 x i64>
    // CHECK: "llvm.mlir.constant"() <{"value" = dense<[32, 64]> : vector<2xi64>}> : () -> !llvm.array<2 x i64>
    %3 = "llvm.mlir.constant"() <{value = dense<0> : vector<[4]xi8>}> : () -> !llvm.array<4 x i8>
    // CHECK: "llvm.mlir.constant"() <{"value" = dense<0> : vector<[4]xi8>}> : () -> !llvm.array<4 x i8>
}) : () -> ()

