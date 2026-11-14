"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "rotl_i32"}> ({
    %3 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %4 = "wasmssa.const"() <{value = 3 : i32}> : () -> i32
    %5 = "wasmssa.rotl"(%3, %4) : (i32, i32) -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "rotl_i64"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.const"() <{value = 3 : i64}> : () -> i64
    %2 = "wasmssa.rotl"(%0, %1) : (i64, i64) -> i64
    "wasmssa.return"(%2) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
