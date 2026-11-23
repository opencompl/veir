"builtin.module"() ({
  "wasmssa.func"() <{functionType = (i32) -> i32, sym_name = "func_0"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i32>):
    %1 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i32>) -> i32
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
  "wasmssa.table"() <{sym_name = "table_0", type = !wasmssa<tabletype !wasmssa.funcref [2:]>}> : () -> ()
  "wasmssa.memory"() <{limits = !wasmssa<limit[0: 65536]>, sym_name = "mem_0"}> : () -> ()
  "wasmssa.global"() <{sym_name = "global_0", type = i32}> ({
    %0 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    "wasmssa.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
