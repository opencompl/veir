"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "clz_i32"}> ({
    %2 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %3 = "wasmssa.clz"(%2) : (i32) -> i32
    "wasmssa.return"(%3) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "clz_i64"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.clz"(%0) : (i64) -> i64
    "wasmssa.return"(%1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
