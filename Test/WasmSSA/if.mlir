"builtin.module"() ({
  "wasmssa.func"() <{functionType = (i32) -> i32, sym_name = "func_0"}> ({
  ^bb0(%arg4: !wasmssa<local ref to i32>):
    %19 = "wasmssa.local_get"(%arg4) : (!wasmssa<local ref to i32>) -> i32
    %20 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
    %21 = "wasmssa.and"(%19, %20) : (i32, i32) -> i32
    "wasmssa.if"(%21)[^bb1] ({
      %26 = "wasmssa.local_get"(%arg4) : (!wasmssa<local ref to i32>) -> i32
      %27 = "wasmssa.const"() <{value = 3 : i32}> : () -> i32
      %28 = "wasmssa.mul"(%26, %27) : (i32, i32) -> i32
      %29 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %30 = "wasmssa.add"(%28, %29) : (i32, i32) -> i32
      "wasmssa.block_return"(%30) : (i32) -> ()
    }, {
      %23 = "wasmssa.local_get"(%arg4) : (!wasmssa<local ref to i32>) -> i32
      %24 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %25 = "wasmssa.shr_u"(%23, %24) : (i32, i32) -> i32
      "wasmssa.block_return"(%25) : (i32) -> ()
    }) : (i32) -> ()
  ^bb1(%22: i32):  // pred: ^bb0
    "wasmssa.return"(%22) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = (i32) -> i32, sym_name = "func_1"}> ({
  ^bb0(%arg2: !wasmssa<local ref to i32>):
    %12 = "wasmssa.local_get"(%arg2) : (!wasmssa<local ref to i32>) -> i32
    %13 = "wasmssa.local_get"(%arg2) : (!wasmssa<local ref to i32>) -> i32
    %14 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
    %15 = "wasmssa.and"(%13, %14) : (i32, i32) -> i32
    "wasmssa.if"(%15, %12)[^bb1] ({
    ^bb0(%arg3: i32):
      %17 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %18 = "wasmssa.add"(%arg3, %17) : (i32, i32) -> i32
      "wasmssa.block_return"(%18) : (i32) -> ()
    }, {
    }) : (i32, i32) -> ()
  ^bb1(%16: i32):  // pred: ^bb0
    "wasmssa.return"(%16) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = (i32) -> i32, sym_name = "func_2"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i32>):
    %0 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i32>) -> i32
    %1 = "wasmssa.ctz"(%0) : (i32) -> i32
    "wasmssa.if"(%1)[^bb1] ({
      %4 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
      %5 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i32>) -> i32
      %6 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      %7 = "wasmssa.shr_u"(%5, %6) : (i32, i32) -> i32
      %8 = "wasmssa.ctz"(%7) : (i32) -> i32
      "wasmssa.if"(%8, %4)[^bb1] ({
      ^bb0(%arg1: i32):
        %10 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
        %11 = "wasmssa.add"(%arg1, %10) : (i32, i32) -> i32
        "wasmssa.block_return"(%11) : (i32) -> ()
      }, {
      }) : (i32, i32) -> ()
    ^bb1(%9: i32):  // pred: ^bb0
      "wasmssa.block_return"(%9) : (i32) -> ()
    }, {
      %3 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
      "wasmssa.block_return"(%3) : (i32) -> ()
    }) : (i32) -> ()
  ^bb1(%2: i32):  // pred: ^bb0
    "wasmssa.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
