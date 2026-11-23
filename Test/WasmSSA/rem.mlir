"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "rem_u_i32"}> ({
    %9 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %10 = "wasmssa.const"() <{value = 3 : i32}> : () -> i32
    %11 = "wasmssa.rem_ui"(%9, %10) : (i32, i32) -> i32
    "wasmssa.return"(%11) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "rem_u_i64"}> ({
    %6 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %7 = "wasmssa.const"() <{value = 3 : i64}> : () -> i64
    %8 = "wasmssa.rem_ui"(%6, %7) : (i64, i64) -> i64
    "wasmssa.return"(%8) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "rem_s_i32"}> ({
    %3 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %4 = "wasmssa.const"() <{value = 3 : i32}> : () -> i32
    %5 = "wasmssa.rem_si"(%3, %4) : (i32, i32) -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "rem_s_i64"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.const"() <{value = 3 : i64}> : () -> i64
    %2 = "wasmssa.rem_si"(%0, %1) : (i64, i64) -> i64
    "wasmssa.return"(%2) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
