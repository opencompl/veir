"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    "wasmssa.block"()[^bb1] ({
      %1 = "wasmssa.const"() <{value = 17 : i32}> : () -> i32
      "wasmssa.block_return"(%1) : (i32) -> ()
    }) : () -> ()
  ^bb1(%0: i32):  // pred: ^bb0
    "wasmssa.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
