// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// As in MLIR, a vector operand is a scalar: it has rank 0 and is passed to the body as is.

// CHECK:      %{{.*}} = "linalg.generic"({{.*}}) <{"indexing_maps" = [affine_map<() -> ()>, affine_map<() -> ()>], "iterator_types" = [], "operandSegmentSizes" = array<i32: 1, 1>}> ({
// CHECK-NEXT: ^{{.*}}(%{{[^ ]+}} : vector<4xf32>, %{{[^ ]+}} : f32):
// CHECK-NEXT:   "linalg.yield"(%{{.*}}) : (f32) -> ()
// CHECK-NEXT: }) : (vector<4xf32>, tensor<f32>) -> tensor<f32>

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (vector<4xf32>, tensor<f32>) -> ()}> ({
  ^bb0(%a: vector<4xf32>, %b: tensor<f32>):
    %0 = "linalg.generic"(%a, %b) <{indexing_maps = [affine_map<() -> ()>, affine_map<() -> ()>], iterator_types = [], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%x: vector<4xf32>, %y: f32):
      "linalg.yield"(%y) : (f32) -> ()
    }) : (vector<4xf32>, tensor<f32>) -> tensor<f32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
