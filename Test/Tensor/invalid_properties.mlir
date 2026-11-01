// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: tensor: expected no properties, but got 1 property
"builtin.module"() ({
  %0 = "tensor.empty"() <{unexpected = true}> : () -> tensor<3x3xf32>
}) : () -> ()
