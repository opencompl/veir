"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_0"}> ({
    %12 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %13 = "wasmssa.extend_i32_s"(%12) : (i32) -> i64
    "wasmssa.return"(%13) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_1"}> ({
    %10 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %11 = "wasmssa.extend_i32_u"(%10) : (i32) -> i64
    "wasmssa.return"(%11) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_2"}> ({
    %8 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %9 = "wasmssa.extend"(%8) <{bitsToTake = 8 : ui32}> : (i32) -> i32
    "wasmssa.return"(%9) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_3"}> ({
    %6 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %7 = "wasmssa.extend"(%6) <{bitsToTake = 16 : ui32}> : (i32) -> i32
    "wasmssa.return"(%7) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_4"}> ({
    %4 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %5 = "wasmssa.extend"(%4) <{bitsToTake = 8 : ui32}> : (i64) -> i64
    "wasmssa.return"(%5) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_5"}> ({
    %2 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %3 = "wasmssa.extend"(%2) <{bitsToTake = 16 : ui32}> : (i64) -> i64
    "wasmssa.return"(%3) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_6"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.extend"(%0) <{bitsToTake = 32 : ui32}> : (i64) -> i64
    "wasmssa.return"(%1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
