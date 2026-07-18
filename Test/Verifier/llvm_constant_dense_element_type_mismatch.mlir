// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %0 = "llvm.mlir.constant"() <{value = dense<0> : tensor<4xi16>}> : () -> !llvm.array<4 x i8>
}) : () -> ()

// CHECK: dense elements type 'i16' does not match array element type 'i8'
