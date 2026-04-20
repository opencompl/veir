"builtin.module"() ({
  "cuda_tile.module"() <{sym_name = "kernels"}> ({
    "cuda_tile.testing$func"() <{arg_attrs = [{}], function_type = (!cuda_tile.ptr<i1>) -> (), sym_name = "test_ptr_types"}> ({
    ^bb0(%arg19: !cuda_tile.ptr<i1>):
      "cuda_tile.return"() : () -> ()
    }) : () -> ()
    "cuda_tile.testing$func"() <{arg_attrs = [{}, {}], function_type = (!cuda_tile.tile<2xf32>, !cuda_tile.tile<f32>) -> (), sym_name = "test_tile_types"}> ({
    ^bb0(%arg17: !cuda_tile.tile<2xf32>, %arg18: !cuda_tile.tile<f32>):
      "cuda_tile.return"() : () -> ()
    }) : () -> ()
    "cuda_tile.testing$func"() <{arg_attrs = [{}, {}, {}, {}, {}, {}, {}], function_type = (!cuda_tile.tensor_view<f32>, !cuda_tile.tensor_view<2xf32, strides=[1]>, !cuda_tile.tensor_view<?x2xf32, strides=[1,?]>, !cuda_tile.tensor_view<?x?xf32, strides=[?,?]>, !cuda_tile.tensor_view<4x?xf32, strides=[5,?]>, !cuda_tile.tensor_view<4x?xf32, strides=[5,?]>, !cuda_tile.tensor_view<f32>) -> (), sym_name = "test_tensor_view_types"}> ({
    ^bb0(%arg10: !cuda_tile.tensor_view<f32>, %arg11: !cuda_tile.tensor_view<2xf32, strides=[1]>, %arg12: !cuda_tile.tensor_view<?x2xf32, strides=[1,?]>, %arg13: !cuda_tile.tensor_view<?x?xf32, strides=[?,?]>, %arg14: !cuda_tile.tensor_view<4x?xf32, strides=[5,?]>, %arg15: !cuda_tile.tensor_view<4x?xf32, strides=[5,?]>, %arg16: !cuda_tile.tensor_view<f32>):
      "cuda_tile.return"() : () -> ()
    }) : () -> ()
    "cuda_tile.testing$func"() <{arg_attrs = [{}, {}, {}, {}, {}, {}, {}, {}, {}, {}], function_type = (!cuda_tile.partition_view<tile=(2), tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), padding_value = zero, tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), padding_value = nan, tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), padding_value = neg_zero, tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), padding_value = pos_inf, tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), padding_value = neg_inf, tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2), tensor_view<16xf32, strides=[1]>>, !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>>, !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>>, !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>, dim_map=[1, 0]>) -> (), sym_name = "test_tile_partition_view_types"}> ({
    ^bb0(%arg0: !cuda_tile.partition_view<tile=(2), tensor_view<16xf32, strides=[1]>>, %arg1: !cuda_tile.partition_view<tile=(2), padding_value = zero, tensor_view<16xf32, strides=[1]>>, %arg2: !cuda_tile.partition_view<tile=(2), padding_value = nan, tensor_view<16xf32, strides=[1]>>, %arg3: !cuda_tile.partition_view<tile=(2), padding_value = neg_zero, tensor_view<16xf32, strides=[1]>>, %arg4: !cuda_tile.partition_view<tile=(2), padding_value = pos_inf, tensor_view<16xf32, strides=[1]>>, %arg5: !cuda_tile.partition_view<tile=(2), padding_value = neg_inf, tensor_view<16xf32, strides=[1]>>, %arg6: !cuda_tile.partition_view<tile=(2), tensor_view<16xf32, strides=[1]>>, %arg7: !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>>, %arg8: !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>>, %arg9: !cuda_tile.partition_view<tile=(2x2), tensor_view<16x16xf32, strides=[16,1]>, dim_map=[1, 0]>):
      "cuda_tile.return"() : () -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

