// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<4xf32>, tensor<4xi32>) -> ()}> ({
  ^bb0(%a: tensor<4xf32>, %b: tensor<4xi32>):
    %0 = "linalg.generic"(%a, %b) <{indexing_maps = [affine_map<(d0) -> (d0)>, affine_map<(d0) -> (d0)>], iterator_types = [#linalg.iterator_type<parallel>], operandSegmentSizes = array<i32: 1, 1>}> ({
    ^bb0(%x: f32, %y: i32):
      "linalg.yield"(%x) : (f32) -> ()
    }) : (tensor<4xf32>, tensor<4xi32>) -> tensor<4xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: linalg.yield: expected operand 0 to have the output element type i32, but found f32
