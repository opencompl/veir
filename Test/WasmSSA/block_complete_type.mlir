"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %0 = "wasmssa.const"() <{value = 14 : i32}> : () -> i32
    "wasmssa.block"(%0)[^bb1] ({
    ^bb0(%arg0: i32):
      %2 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %3 = "wasmssa.add"(%arg0, %2) : (i32, i32) -> i32
      "wasmssa.block_return"(%3) : (i32) -> ()
    }) : (i32) -> ()
  ^bb1(%1: i32):  // pred: ^bb0
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
