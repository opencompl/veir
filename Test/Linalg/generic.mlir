// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0, d1)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>], "operandSegmentSizes" = array<i32: 2, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : i32, %{{[^ ]+}} : i32, %{{[^ ]+}} : i32):
// CHECK:      "linalg.yield"({{.*}}) : (i32) -> ()
// CHECK-NEXT: }) : (tensor<4x8xi32>, tensor<4x8xi32>, tensor<4x8xi32>) -> tensor<4x8xi32>
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : i32, %{{[^ ]+}} : i32):
// CHECK:      "linalg.yield"({{.*}}) : (i32) -> ()
// CHECK-NEXT: }) : (tensor<4x8xi32>, tensor<4xi32>) -> tensor<4xi32>
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<(d0, d1) -> ()>, affine_map<(d0, d1) -> (d0, d1)>], "iterator_types" = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>], "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (f32, tensor<4x8xf32>) -> tensor<4x8xf32>
// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"doc" = "copy a column", "indexing_maps" = [affine_map<(d0) -> (d0, 0)>, affine_map<(d0) -> (d0)>], "iterator_types" = [#linalg.iterator_type<parallel>], "library_call" = "copy_column", "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : f32, %{{[^ ]+}} : f32):
// CHECK:      "linalg.yield"({{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (tensor<4x1xf32>, tensor<4xf32>) -> tensor<4xf32>

"builtin.module"() ({
  // Elementwise addition.
  "func.func"() <{function_type = (tensor<4x8xi32>, tensor<4x8xi32>) -> tensor<4x8xi32>, sym_name = "add"}> ({
  ^bb0(%a: tensor<4x8xi32>, %b: tensor<4x8xi32>):
    %init = "tensor.empty"() : () -> tensor<4x8xi32>
    %0 = "linalg.generic"(%a, %b, %init) <{indexing_maps = [affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0, d1)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>], operandSegmentSizes = array<i32: 2, 1>}> ({
    ^bb0(%x: i32, %y: i32, %out: i32):
      %s = "arith.addi"(%x, %y) : (i32, i32) -> i32
      "linalg.yield"(%s) : (i32) -> ()
    }) : (tensor<4x8xi32>, tensor<4x8xi32>, tensor<4x8xi32>) -> tensor<4x8xi32>
    "func.return"(%0) : (tensor<4x8xi32>) -> ()
  }) : () -> ()

  // Sum of every row of a matrix.
  "func.func"() <{function_type = (tensor<4x8xi32>, tensor<4xi32>) -> tensor<4xi32>, sym_name = "row_sum"}> ({
  ^bb0(%a: tensor<4x8xi32>, %init: tensor<4xi32>):
    %0 = "linalg.generic"(%a, %init) <{indexing_maps = [affine_map<(d0, d1) -> (d0, d1)>, affine_map<(d0, d1) -> (d0)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<reduction>], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%x: i32, %acc: i32):
      %s = "arith.addi"(%x, %acc) : (i32, i32) -> i32
      "linalg.yield"(%s) : (i32) -> ()
    }) : (tensor<4x8xi32>, tensor<4xi32>) -> tensor<4xi32>
    "func.return"(%0) : (tensor<4xi32>) -> ()
  }) : () -> ()

  // Fill with a scalar input, broadcast over every element.
  "func.func"() <{function_type = (f32) -> tensor<4x8xf32>, sym_name = "fill"}> ({
  ^bb0(%v: f32):
    %init = "tensor.empty"() : () -> tensor<4x8xf32>
    %0 = "linalg.generic"(%v, %init) <{indexing_maps = [affine_map<(d0, d1) -> ()>, affine_map<(d0, d1) -> (d0, d1)>], iterator_types = [#linalg.iterator_type<parallel>, #linalg.iterator_type<parallel>], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%x: f32, %out: f32):
      "linalg.yield"(%x) : (f32) -> ()
    }) : (f32, tensor<4x8xf32>) -> tensor<4x8xf32>
    "func.return"(%0) : (tensor<4x8xf32>) -> ()
  }) : () -> ()

  // Documentation and a library call, with a constant index into a unit dimension.
  "func.func"() <{function_type = (tensor<4x1xf32>, tensor<4xf32>) -> tensor<4xf32>, sym_name = "doc"}> ({
  ^bb0(%a: tensor<4x1xf32>, %init: tensor<4xf32>):
    %0 = "linalg.generic"(%a, %init) <{doc = "copy a column", indexing_maps = [affine_map<(d0) -> (d0, 0)>, affine_map<(d0) -> (d0)>], iterator_types = [#linalg.iterator_type<parallel>], library_call = "copy_column", operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%x: f32, %out: f32):
      "linalg.yield"(%x) : (f32) -> ()
    }) : (tensor<4x1xf32>, tensor<4xf32>) -> tensor<4xf32>
    "func.return"(%0) : (tensor<4xf32>) -> ()
  }) : () -> ()
}) : () -> ()
