// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// The output of mlir/test/Dialect/Linalg/generalize-named-ops.mlir at LLVM tag
// llvmorg-23.1.2 for the cases that are within the subset VeIR supports, i.e. on
// static tensors. Each case was converted with
// `mlir-opt -linalg-generalize-named-ops --mlir-print-op-generic --mlir-print-local-scope`.
// VeIR does not support the float `arith` operations in the bodies, so they are
// parsed as unregistered operations. `generalize_matmul_tensor_complex` is left
// out, since VeIR has no `complex` type; all other cases use memrefs or dynamic
// shapes.

// CHECK-LABEL: "sym_name" = "generalize_matmul_tensor"
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1)>, affine_map<(d0, d1, d2) -> (d0, d1)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], "operandSegmentSizes" = array<i32: 2, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>
// CHECK-LABEL: "sym_name" = "fill_tensor"
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<() -> ()>, affine_map<() -> ()>], "iterator_types" = [], "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (f32, tensor<f32>) -> tensor<f32>
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<() -> ()>, affine_map<() -> ()>], "iterator_types" = [], "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : vector<2x4xf32>, %{{[^ ]+}} : vector<2x4xf32>):
// CHECK:      "linalg.yield"({{.*}}) : (vector<2x4xf32>) -> ()
// CHECK-NEXT: }) : (vector<2x4xf32>, tensor<vector<2x4xf32>>) -> tensor<vector<2x4xf32>>
// CHECK-LABEL: "sym_name" = "batch_matmul"
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1, d2, d3) -> (d0, d1, d3)>, affine_map<(d0, d1, d2, d3) -> (d0, d3, d2)>, affine_map<(d0, d1, d2, d3) -> (d0, d1, d2)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], "operandSegmentSizes" = array<i32: 2, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<2x3x7xf32>) -> tensor<2x3x7xf32>
// CHECK-LABEL: "sym_name" = "batch_reduce_matmul"
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1, d2, d3) -> (d0, d1, d3)>, affine_map<(d0, d1, d2, d3) -> (d0, d3, d2)>, affine_map<(d0, d1, d2, d3) -> (d1, d2)>], "iterator_types" = [#linalg.iterator_type<reduction>, #linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], "operandSegmentSizes" = array<i32: 2, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<3x7xf32>) -> tensor<3x7xf32>
// CHECK-LABEL: "sym_name" = "preserve_discardable_attrs"
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1)>, affine_map<(d0, d1, d2) -> (d0, d1)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], "operandSegmentSizes" = array<i32: 2, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) {"another_attr" = 42 : i64, "my_custom_attr" = "preserved"} : (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>

"builtin.module"() ({
  "func.func"() <{function_type = (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>, sym_name = "generalize_matmul_tensor"}> ({
  ^bb0(%arg0: tensor<16x8xf32>, %arg1: tensor<8x32xf32>, %arg2: tensor<16x32xf32>):
    %0 = "linalg.generic"(%arg0, %arg1, %arg2) <{indexing_maps = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1)>, affine_map<(d0, d1, d2) -> (d0, d1)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], operandSegmentSizes = array<i32: 2, 1>}> ({
    ^bb0(%arg3: f32, %arg4: f32, %arg5: f32):
      %1 = "arith.mulf"(%arg3, %arg4) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      %2 = "arith.addf"(%arg5, %1) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      "linalg.yield"(%2) : (f32) -> ()
    }) : (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>
    "func.return"(%0) : (tensor<16x32xf32>) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (f32, vector<2x4xf32>) -> (tensor<f32>, tensor<vector<2x4xf32>>), sym_name = "fill_tensor"}> ({
  ^bb0(%arg0: f32, %arg1: vector<2x4xf32>):
    %0 = "tensor.empty"() : () -> tensor<f32>
    %1 = "linalg.generic"(%arg0, %0) <{indexing_maps = [affine_map<() -> ()>, affine_map<() -> ()>], iterator_types = [], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%arg4: f32, %arg5: f32):
      "linalg.yield"(%arg4) : (f32) -> ()
    }) : (f32, tensor<f32>) -> tensor<f32>
    %2 = "tensor.empty"() : () -> tensor<vector<2x4xf32>>
    %3 = "linalg.generic"(%arg1, %2) <{indexing_maps = [affine_map<() -> ()>, affine_map<() -> ()>], iterator_types = [], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%arg2: vector<2x4xf32>, %arg3: vector<2x4xf32>):
      "linalg.yield"(%arg2) : (vector<2x4xf32>) -> ()
    }) : (vector<2x4xf32>, tensor<vector<2x4xf32>>) -> tensor<vector<2x4xf32>>
    "func.return"(%1, %3) : (tensor<f32>, tensor<vector<2x4xf32>>) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<2x3x7xf32>) -> tensor<2x3x7xf32>, sym_name = "batch_matmul"}> ({
  ^bb0(%arg0: tensor<2x3x5xf32>, %arg1: tensor<2x5x7xf32>, %arg2: tensor<2x3x7xf32>):
    %0 = "linalg.generic"(%arg0, %arg1, %arg2) <{indexing_maps = [affine_map<(d0, d1, d2, d3) -> (d0, d1, d3)>, affine_map<(d0, d1, d2, d3) -> (d0, d3, d2)>, affine_map<(d0, d1, d2, d3) -> (d0, d1, d2)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], operandSegmentSizes = array<i32: 2, 1>}> ({
    ^bb0(%arg3: f32, %arg4: f32, %arg5: f32):
      %1 = "arith.mulf"(%arg3, %arg4) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      %2 = "arith.addf"(%arg5, %1) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      "linalg.yield"(%2) : (f32) -> ()
    }) : (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<2x3x7xf32>) -> tensor<2x3x7xf32>
    "func.return"(%0) : (tensor<2x3x7xf32>) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<3x7xf32>) -> tensor<3x7xf32>, sym_name = "batch_reduce_matmul"}> ({
  ^bb0(%arg0: tensor<2x3x5xf32>, %arg1: tensor<2x5x7xf32>, %arg2: tensor<3x7xf32>):
    %0 = "linalg.generic"(%arg0, %arg1, %arg2) <{indexing_maps = [affine_map<(d0, d1, d2, d3) -> (d0, d1, d3)>, affine_map<(d0, d1, d2, d3) -> (d0, d3, d2)>, affine_map<(d0, d1, d2, d3) -> (d1, d2)>], iterator_types = [#linalg.iterator_type<reduction>, #linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], operandSegmentSizes = array<i32: 2, 1>}> ({
    ^bb0(%arg3: f32, %arg4: f32, %arg5: f32):
      %1 = "arith.mulf"(%arg3, %arg4) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      %2 = "arith.addf"(%arg5, %1) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      "linalg.yield"(%2) : (f32) -> ()
    }) : (tensor<2x3x5xf32>, tensor<2x5x7xf32>, tensor<3x7xf32>) -> tensor<3x7xf32>
    "func.return"(%0) : (tensor<3x7xf32>) -> ()
  }) : () -> ()
  "func.func"() <{function_type = (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>, sym_name = "preserve_discardable_attrs"}> ({
  ^bb0(%arg0: tensor<16x8xf32>, %arg1: tensor<8x32xf32>, %arg2: tensor<16x32xf32>):
    %0 = "linalg.generic"(%arg0, %arg1, %arg2) <{indexing_maps = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1)>, affine_map<(d0, d1, d2) -> (d0, d1)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], operandSegmentSizes = array<i32: 2, 1>}> ({
    ^bb0(%arg3: f32, %arg4: f32, %arg5: f32):
      %1 = "arith.mulf"(%arg3, %arg4) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      %2 = "arith.addf"(%arg5, %1) <{fastmath = #arith.fastmath<none>}> : (f32, f32) -> f32
      "linalg.yield"(%2) : (f32) -> ()
    }) {another_attr = 42 : i64, my_custom_attr = "preserved"} : (tensor<16x8xf32>, tensor<8x32xf32>, tensor<16x32xf32>) -> tensor<16x32xf32>
    "func.return"(%0) : (tensor<16x32xf32>) -> ()
  }) : () -> ()
}) : () -> ()
