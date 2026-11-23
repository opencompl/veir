"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "eqz_i32"}> ({
    %2 = "wasmssa.const"() <{value = 13 : i32}> : () -> i32
    %3 = "wasmssa.eqz"(%2) : (i32) -> i32
    "wasmssa.return"(%3) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "eqz_i64"}> ({
    %0 = "wasmssa.const"() <{value = 13 : i64}> : () -> i64
    %1 = "wasmssa.eqz"(%0) : (i64) -> i32
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
