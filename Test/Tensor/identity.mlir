// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// CHECK:      ^{{.*}}(%[[T:[^ ]+]] : tensor<4x8xf32>, %[[F:[^ ]+]] : f32):
// CHECK-NEXT: %[[C0:[^ ]+]] = "arith.constant"() <{"value" = 0 : index}> : () -> index
// CHECK-NEXT: %[[C1:[^ ]+]] = "arith.constant"() <{"value" = 1 : index}> : () -> index
// CHECK-NEXT: "tensor.empty"() : () -> tensor<3x3xf32>
// CHECK-NEXT: "tensor.empty"() : () -> tensor<0x4xf32>
// CHECK-NEXT: "tensor.extract"(%[[T]], %[[C0]], %[[C1]]) : (tensor<4x8xf32>, index, index) -> f32
// CHECK-NEXT: "tensor.insert"(%[[F]], %[[T]], %[[C0]], %[[C1]]) : (f32, tensor<4x8xf32>, index, index) -> tensor<4x8xf32>

"builtin.module"() ({
  "func.func"() <{function_type = (tensor<4x8xf32>, f32) -> (), sym_name = "all"}> ({
  ^bb0(%t: tensor<4x8xf32>, %f: f32):
    %c0 = "arith.constant"() <{value = 0 : index}> : () -> index
    %c1 = "arith.constant"() <{value = 1 : index}> : () -> index
    %0 = "tensor.empty"() : () -> tensor<3x3xf32>
    %z = "tensor.empty"() : () -> tensor<0x4xf32>
    %1 = "tensor.extract"(%t, %c0, %c1) : (tensor<4x8xf32>, index, index) -> f32
    %2 = "tensor.insert"(%f, %t, %c0, %c1) : (f32, tensor<4x8xf32>, index, index) -> tensor<4x8xf32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
