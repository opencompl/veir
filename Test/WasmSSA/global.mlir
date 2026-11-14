"builtin.module"() ({
  "wasmssa.import_global"() <{importName = "from_js", moduleName = "env", sym_name = "global_0", type = i32}> : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %6 = "wasmssa.global_get"() <{global = @global_0}> : () -> i32
    %7 = "wasmssa.global_get"() <{global = @global_1}> : () -> i32
    %8 = "wasmssa.add"(%6, %7) : (i32, i32) -> i32
    %9 = "wasmssa.global_get"() <{global = @global_2}> : () -> i32
    %10 = "wasmssa.global_get"() <{global = @global_3}> : () -> i32
    %11 = "wasmssa.add"(%9, %10) : (i32, i32) -> i32
    %12 = "wasmssa.add"(%8, %11) : (i32, i32) -> i32
    "wasmssa.return"(%12) : (i32) -> ()
  }) : () -> ()
  "wasmssa.global"() <{sym_name = "global_1", type = i32}> ({
    %5 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.global"() <{isMutable, sym_name = "global_2", type = i32}> ({
    %4 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    "wasmssa.return"(%4) : (i32) -> ()
  }) : () -> ()
  "wasmssa.global"() <{isMutable, sym_name = "global_3", type = i32}> ({
    %3 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    "wasmssa.return"(%3) : (i32) -> ()
  }) : () -> ()
  "wasmssa.global"() <{sym_name = "global_4", type = i64}> ({
    %2 = "wasmssa.const"() <{value = 11 : i64}> : () -> i64
    "wasmssa.return"(%2) : (i64) -> ()
  }) : () -> ()
  "wasmssa.global"() <{sym_name = "global_5", type = f32}> ({
    %1 = "wasmssa.const"() <{value = 1.200000e+01 : f32}> : () -> f32
    "wasmssa.return"(%1) : (f32) -> ()
  }) : () -> ()
  "wasmssa.global"() <{sym_name = "global_6", type = f64}> ({
    %0 = "wasmssa.const"() <{value = 1.300000e+01 : f64}> : () -> f64
    "wasmssa.return"(%0) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
