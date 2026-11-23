"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "ctz_i32"}> ({
    %2 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %3 = "wasmssa.ctz"(%2) : (i32) -> i32
    "wasmssa.return"(%3) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "ctz_i64"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.ctz"(%0) : (i64) -> i64
    "wasmssa.return"(%1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
