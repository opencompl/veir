"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> (), sym_name = "func_0"}> ({
    %0 = "wasmssa.local"() <{type = i32}> : () -> !wasmssa<local ref to i32>
    %1 = "wasmssa.local"() <{type = i32}> : () -> !wasmssa<local ref to i32>
    "wasmssa.loop"()[^bb1] ({
      %2 = "wasmssa.local_get"(%0) : (!wasmssa<local ref to i32>) -> i32
      %3 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %4 = "wasmssa.add"(%2, %3) : (i32, i32) -> i32
      "wasmssa.local_set"(%0, %4) : (!wasmssa<local ref to i32>, i32) -> ()
      "wasmssa.loop"()[^bb1] ({
        %8 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
        %9 = "wasmssa.local_get"(%1) : (!wasmssa<local ref to i32>) -> i32
        %10 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
        %11 = "wasmssa.add"(%9, %10) : (i32, i32) -> i32
        %12 = "wasmssa.local_tee"(%1, %11) : (!wasmssa<local ref to i32>, i32) -> i32
        %13 = "wasmssa.local_get"(%0) : (!wasmssa<local ref to i32>) -> i32
        %14 = "wasmssa.gt_si"(%12, %13) : (i32, i32) -> i32
        "wasmssa.branch_if"(%14)[^bb1] <{exitLevel = 0 : ui32}> : (i32) -> ()
      ^bb1:  // pred: ^bb0
        "wasmssa.block_return"(%8) : (i32) -> ()
      }) : () -> ()
    ^bb1(%5: i32):  // pred: ^bb0
      %6 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
      %7 = "wasmssa.lt_si"(%5, %6) : (i32, i32) -> i32
      "wasmssa.branch_if"(%7)[^bb2] <{exitLevel = 0 : ui32}> : (i32) -> ()
    ^bb2:  // pred: ^bb1
      "wasmssa.block_return"() : () -> ()
    }) : () -> ()
  ^bb1:  // pred: ^bb0
    "wasmssa.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
