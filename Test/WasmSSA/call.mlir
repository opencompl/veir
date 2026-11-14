"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %1 = "wasmssa.const"() <{value = 42 : i32}> : () -> i32
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "forty_two"}> ({
    %0 = "wasmssa.call"() <{callee = @func_0}> : () -> i32
    "wasmssa.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
