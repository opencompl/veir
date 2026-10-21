// RUN: VEIR_ROUNDTRIP

// CHECK:      "tensor.empty"() : () -> tensor<3x3xf32>
// CHECK-NEXT: "tensor.empty"() : () -> tensor<0x4xf32>

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "empty"}> ({
    %0 = "tensor.empty"() : () -> tensor<3x3xf32>
    %z = "tensor.empty"() : () -> tensor<0x4xf32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
