// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: invalid properties for op tensor.empty: this operation has empty properties
"builtin.module"() ({
  %0 = "tensor.empty"() <{unexpected = true}> : () -> tensor<3x3xf32>
}) : () -> ()
