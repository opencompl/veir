"builtin.module"() ({
  "wasmssa.import_func"() <{importName = "twoTimes", moduleName = "env", sym_name = "func_0", type = (i32) -> i32}> : () -> ()
  "wasmssa.func"() <{exported, functionType = (i32, i32) -> i32, sym_name = "add"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i32>, %arg1: !wasmssa<local ref to i32>):
    %1 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i32>) -> i32
    %2 = "wasmssa.call"(%1) <{callee = @func_0}> : (i32) -> i32
    %3 = "wasmssa.local_get"(%arg1) : (!wasmssa<local ref to i32>) -> i32
    %4 = "wasmssa.call"(%3) <{callee = @func_0}> : (i32) -> i32
    %5 = "wasmssa.add"(%2, %4) : (i32, i32) -> i32
    %6 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
    %7 = "wasmssa.div_si"(%5, %6) : (i32, i32) -> i32
    "wasmssa.return"(%7) : (i32) -> ()
  }) : () -> ()
  "wasmssa.memory"() <{exported, limits = !wasmssa<limit[2:]>, sym_name = "memory"}> : () -> ()
  "wasmssa.global"() <{isMutable, sym_name = "global_0", type = i32}> ({
    %0 = "wasmssa.const"() <{value = 66560 : i32}> : () -> i32
    "wasmssa.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
