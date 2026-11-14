"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_sat_f32_s"}> ({
    %14 = "wasmssa.const"() <{value = 1.210000e+01 : f32}> : () -> f32
    %15 = "wasmssa.trunc_sat_si"(%14) : (f32) -> i32
    "wasmssa.return"(%15) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_sat_f32_u"}> ({
    %12 = "wasmssa.const"() <{value = 1.210000e+01 : f32}> : () -> f32
    %13 = "wasmssa.trunc_sat_ui"(%12) : (f32) -> i32
    "wasmssa.return"(%13) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_sat_f64_s"}> ({
    %10 = "wasmssa.const"() <{value = 1.210000e+01 : f64}> : () -> f64
    %11 = "wasmssa.trunc_sat_si"(%10) : (f64) -> i32
    "wasmssa.return"(%11) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "trunc_sat_f64_u"}> ({
    %8 = "wasmssa.const"() <{value = 1.210000e+01 : f64}> : () -> f64
    %9 = "wasmssa.trunc_sat_ui"(%8) : (f64) -> i32
    "wasmssa.return"(%9) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "i64_trunc_sat_f32_s"}> ({
    %6 = "wasmssa.const"() <{value = 1.210000e+01 : f32}> : () -> f32
    %7 = "wasmssa.trunc_sat_si"(%6) : (f32) -> i64
    "wasmssa.return"(%7) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "i64_trunc_sat_f32_u"}> ({
    %4 = "wasmssa.const"() <{value = 1.210000e+01 : f32}> : () -> f32
    %5 = "wasmssa.trunc_sat_ui"(%4) : (f32) -> i64
    "wasmssa.return"(%5) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "i64_trunc_sat_f64_s"}> ({
    %2 = "wasmssa.const"() <{value = 1.210000e+01 : f64}> : () -> f64
    %3 = "wasmssa.trunc_sat_si"(%2) : (f64) -> i64
    "wasmssa.return"(%3) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "i64_trunc_sat_f64_u"}> ({
    %0 = "wasmssa.const"() <{value = 1.210000e+01 : f64}> : () -> f64
    %1 = "wasmssa.trunc_sat_ui"(%0) : (f64) -> i64
    "wasmssa.return"(%1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
