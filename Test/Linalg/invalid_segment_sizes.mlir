// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<4xf32>) -> ()}> ({
  ^bb0(%a: tensor<4xf32>):
    %0 = "linalg.generic"(%a, %a) <{indexing_maps = [affine_map<(d0) -> (d0)>, affine_map<(d0) -> (d0)>], iterator_types = [#linalg.iterator_type<parallel>], operandSegmentSizes = array<i32: 1, 2>}> ({
    ^bb0(%x: f32, %y: f32):
      "linalg.yield"(%x) : (f32) -> ()
    }) : (tensor<4xf32>, tensor<4xf32>) -> tensor<4xf32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: linalg.generic: operandSegmentSizes describes 3 operands, got 2
