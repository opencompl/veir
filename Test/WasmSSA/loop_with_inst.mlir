"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %0 = "wasmssa.local"() <{type = i32}> : () -> !wasmssa<local ref to i32>
    "wasmssa.loop"()[^bb1] ({
      %2 = "wasmssa.local_get"(%0) : (!wasmssa<local ref to i32>) -> i32
      %3 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %4 = "wasmssa.add"(%2, %3) : (i32, i32) -> i32
      "wasmssa.local_set"(%0, %4) : (!wasmssa<local ref to i32>, i32) -> ()
      %5 = "wasmssa.local_get"(%0) : (!wasmssa<local ref to i32>) -> i32
      %6 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
      %7 = "wasmssa.lt_si"(%5, %6) : (i32, i32) -> i32
      "wasmssa.block_return"(%7) : (i32) -> ()
    }) : () -> ()
  ^bb1(%1: i32):  // pred: ^bb0
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
