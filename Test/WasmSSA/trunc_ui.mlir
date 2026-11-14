"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_ui_f32_to_i32"}> ({
    %6 = "wasmssa.const"() <{value = 1.000000e+01 : f32}> : () -> f32
    %7 = "wasmssa.trunc_ui"(%6) : (f32) -> i32
    "wasmssa.return"(%7) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_ui_f64_to_i32"}> ({
    %4 = "wasmssa.const"() <{value = 1.000000e+01 : f64}> : () -> f64
    %5 = "wasmssa.trunc_ui"(%4) : (f64) -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "trunc_ui_f32_to_i64"}> ({
    %2 = "wasmssa.const"() <{value = 1.000000e+01 : f32}> : () -> f32
    %3 = "wasmssa.trunc_ui"(%2) : (f32) -> i64
    "wasmssa.return"(%3) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "trunc_ui_f64_to_i64"}> ({
    %0 = "wasmssa.const"() <{value = 1.000000e+01 : f64}> : () -> f64
    %1 = "wasmssa.trunc_ui"(%0) : (f64) -> i64
    "wasmssa.return"(%1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
