"builtin.module"() ({
  "wasmssa.func"() <{functionType = (i32) -> (), sym_name = "func_0"}> ({
  ^bb0(%arg1: !wasmssa<local ref to i32>):
    "wasmssa.block"()[^bb1] ({
      "wasmssa.block"()[^bb1] ({
        "wasmssa.block"()[^bb1] ({
          "wasmssa.block_return"() : () -> ()
        }) : () -> ()
      ^bb1:  // pred: ^bb0
        "wasmssa.block_return"() : () -> ()
      }) : () -> ()
    ^bb1:  // pred: ^bb0
      "wasmssa.block_return"() : () -> ()
    }) : () -> ()
  ^bb1:  // pred: ^bb0
    "wasmssa.return"() : () -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = (i32) -> (), sym_name = "func_1"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i32>):
    "wasmssa.block"()[^bb1] ({
      "wasmssa.block_return"() : () -> ()
    }) : () -> ()
  ^bb1:  // pred: ^bb0
    "wasmssa.block"()[^bb2] ({
      "wasmssa.block_return"() : () -> ()
    }) : () -> ()
  ^bb2:  // pred: ^bb1
    "wasmssa.block"()[^bb3] ({
      "wasmssa.block_return"() : () -> ()
    }) : () -> ()
  ^bb3:  // pred: ^bb2
    "wasmssa.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
