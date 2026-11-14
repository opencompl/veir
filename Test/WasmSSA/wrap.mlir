"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = (i64) -> i32, sym_name = "i64_wrap"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i64>):
    %0 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i64>) -> i64
    %1 = "wasmssa.wrap"(%0) : (i64) -> i32
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
