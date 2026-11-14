"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    "wasmssa.block"()[^bb1] ({
      %1 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %2 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
      "wasmssa.branch_if"(%2, %1)[^bb1] <{exitLevel = 0 : ui32}> : (i32, i32) -> ()
    ^bb1:  // pred: ^bb0
      %3 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %4 = "wasmssa.add"(%1, %3) : (i32, i32) -> i32
      "wasmssa.block_return"(%4) : (i32) -> ()
    }) : () -> ()
  ^bb1(%0: i32):  // pred: ^bb0
    "wasmssa.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
