// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  %0 = "llvm.mlir.constant"() <{value = dense<0> : tensor<4 x i8>}> : () -> !llvm.array<4 x i8>
  %1 = "llvm.mlir.constant"() <{value = dense<0> : tensor<2x3xi8>}> : () -> !llvm.array<2 x array<3 x i8>>
}) : () -> ()

// CHECK: "llvm.mlir.constant"() <{"value" = dense<0> : tensor<4 x i8>}> : () -> !llvm.array<4 x i8>
// CHECK: "llvm.mlir.constant"() <{"value" = dense<0> : tensor<2x3xi8>}> : () -> !llvm.array<2 x !llvm.array<3 x i8>>
