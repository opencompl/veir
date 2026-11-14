"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "div_u_i32"}> ({
    %27 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %28 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
    %29 = "wasmssa.div_ui"(%27, %28) : (i32, i32) -> i32
    "wasmssa.return"(%29) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "div_u_i32_zero"}> ({
    %24 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %25 = "wasmssa.const"() <{value = 0 : i32}> : () -> i32
    %26 = "wasmssa.div_ui"(%24, %25) : (i32, i32) -> i32
    "wasmssa.return"(%26) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "div_s_i32"}> ({
    %21 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %22 = "wasmssa.const"() <{value = 2 : i32}> : () -> i32
    %23 = "wasmssa.div_si"(%21, %22) : (i32, i32) -> i32
    "wasmssa.return"(%23) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "div_s_i32_zero"}> ({
    %18 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %19 = "wasmssa.const"() <{value = 0 : i32}> : () -> i32
    %20 = "wasmssa.div_si"(%18, %19) : (i32, i32) -> i32
    "wasmssa.return"(%20) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "div_u_i64"}> ({
    %15 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %16 = "wasmssa.const"() <{value = 2 : i64}> : () -> i64
    %17 = "wasmssa.div_ui"(%15, %16) : (i64, i64) -> i64
    "wasmssa.return"(%17) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "div_u_i64_zero"}> ({
    %12 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %13 = "wasmssa.const"() <{value = 0 : i64}> : () -> i64
    %14 = "wasmssa.div_ui"(%12, %13) : (i64, i64) -> i64
    "wasmssa.return"(%14) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "div_s_i64"}> ({
    %9 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %10 = "wasmssa.const"() <{value = 2 : i64}> : () -> i64
    %11 = "wasmssa.div_si"(%9, %10) : (i64, i64) -> i64
    "wasmssa.return"(%11) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "div_s_i64_zero"}> ({
    %6 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %7 = "wasmssa.const"() <{value = 0 : i64}> : () -> i64
    %8 = "wasmssa.div_si"(%6, %7) : (i64, i64) -> i64
    "wasmssa.return"(%8) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "div_f32"}> ({
    %3 = "wasmssa.const"() <{value = 1.000000e+01 : f32}> : () -> f32
    %4 = "wasmssa.const"() <{value = 2.000000e+00 : f32}> : () -> f32
    %5 = "wasmssa.div"(%3, %4) : (f32, f32) -> f32
    "wasmssa.return"(%5) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "div_f64"}> ({
    %0 = "wasmssa.const"() <{value = 1.000000e+01 : f64}> : () -> f64
    %1 = "wasmssa.const"() <{value = 2.000000e+00 : f64}> : () -> f64
    %2 = "wasmssa.div"(%0, %1) : (f64, f64) -> f64
    "wasmssa.return"(%2) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
