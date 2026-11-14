"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %69 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %70 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %71 = "wasmssa.lt_si"(%69, %70) : (i32, i32) -> i32
    "wasmssa.return"(%71) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_1"}> ({
    %66 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %67 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %68 = "wasmssa.le_si"(%66, %67) : (i32, i32) -> i32
    "wasmssa.return"(%68) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_2"}> ({
    %63 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %64 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %65 = "wasmssa.lt_ui"(%63, %64) : (i32, i32) -> i32
    "wasmssa.return"(%65) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_3"}> ({
    %60 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %61 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %62 = "wasmssa.le_ui"(%60, %61) : (i32, i32) -> i32
    "wasmssa.return"(%62) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_4"}> ({
    %57 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %58 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %59 = "wasmssa.gt_si"(%57, %58) : (i32, i32) -> i32
    "wasmssa.return"(%59) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_5"}> ({
    %54 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %55 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %56 = "wasmssa.gt_ui"(%54, %55) : (i32, i32) -> i32
    "wasmssa.return"(%56) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_6"}> ({
    %51 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %52 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %53 = "wasmssa.ge_si"(%51, %52) : (i32, i32) -> i32
    "wasmssa.return"(%53) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_7"}> ({
    %48 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %49 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %50 = "wasmssa.ge_ui"(%48, %49) : (i32, i32) -> i32
    "wasmssa.return"(%50) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_8"}> ({
    %45 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %46 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %47 = "wasmssa.lt_si"(%45, %46) : (i64, i64) -> i32
    "wasmssa.return"(%47) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_9"}> ({
    %42 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %43 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %44 = "wasmssa.le_si"(%42, %43) : (i64, i64) -> i32
    "wasmssa.return"(%44) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_10"}> ({
    %39 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %40 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %41 = "wasmssa.lt_ui"(%39, %40) : (i64, i64) -> i32
    "wasmssa.return"(%41) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_11"}> ({
    %36 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %37 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %38 = "wasmssa.le_ui"(%36, %37) : (i64, i64) -> i32
    "wasmssa.return"(%38) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_12"}> ({
    %33 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %34 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %35 = "wasmssa.gt_si"(%33, %34) : (i64, i64) -> i32
    "wasmssa.return"(%35) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_13"}> ({
    %30 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %31 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %32 = "wasmssa.gt_ui"(%30, %31) : (i64, i64) -> i32
    "wasmssa.return"(%32) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_14"}> ({
    %27 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %28 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %29 = "wasmssa.ge_si"(%27, %28) : (i64, i64) -> i32
    "wasmssa.return"(%29) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_15"}> ({
    %24 = "wasmssa.const"() <{value = 12 : i64}> : () -> i64
    %25 = "wasmssa.const"() <{value = 50 : i64}> : () -> i64
    %26 = "wasmssa.ge_ui"(%24, %25) : (i64, i64) -> i32
    "wasmssa.return"(%26) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_16"}> ({
    %21 = "wasmssa.const"() <{value = 5.000000e+00 : f32}> : () -> f32
    %22 = "wasmssa.const"() <{value = 1.400000e+01 : f32}> : () -> f32
    %23 = "wasmssa.lt"(%21, %22) : (f32, f32) -> i32
    "wasmssa.return"(%23) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_17"}> ({
    %18 = "wasmssa.const"() <{value = 5.000000e+00 : f32}> : () -> f32
    %19 = "wasmssa.const"() <{value = 1.400000e+01 : f32}> : () -> f32
    %20 = "wasmssa.le"(%18, %19) : (f32, f32) -> i32
    "wasmssa.return"(%20) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_18"}> ({
    %15 = "wasmssa.const"() <{value = 5.000000e+00 : f32}> : () -> f32
    %16 = "wasmssa.const"() <{value = 1.400000e+01 : f32}> : () -> f32
    %17 = "wasmssa.gt"(%15, %16) : (f32, f32) -> i32
    "wasmssa.return"(%17) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_19"}> ({
    %12 = "wasmssa.const"() <{value = 5.000000e+00 : f32}> : () -> f32
    %13 = "wasmssa.const"() <{value = 1.400000e+01 : f32}> : () -> f32
    %14 = "wasmssa.ge"(%12, %13) : (f32, f32) -> i32
    "wasmssa.return"(%14) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_20"}> ({
    %9 = "wasmssa.const"() <{value = 5.000000e+00 : f64}> : () -> f64
    %10 = "wasmssa.const"() <{value = 1.400000e+01 : f64}> : () -> f64
    %11 = "wasmssa.lt"(%9, %10) : (f64, f64) -> i32
    "wasmssa.return"(%11) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_21"}> ({
    %6 = "wasmssa.const"() <{value = 5.000000e+00 : f64}> : () -> f64
    %7 = "wasmssa.const"() <{value = 1.400000e+01 : f64}> : () -> f64
    %8 = "wasmssa.le"(%6, %7) : (f64, f64) -> i32
    "wasmssa.return"(%8) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_22"}> ({
    %3 = "wasmssa.const"() <{value = 5.000000e+00 : f64}> : () -> f64
    %4 = "wasmssa.const"() <{value = 1.400000e+01 : f64}> : () -> f64
    %5 = "wasmssa.gt"(%3, %4) : (f64, f64) -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_23"}> ({
    %0 = "wasmssa.const"() <{value = 5.000000e+00 : f64}> : () -> f64
    %1 = "wasmssa.const"() <{value = 1.400000e+01 : f64}> : () -> f64
    %2 = "wasmssa.ge"(%0, %1) : (f64, f64) -> i32
    "wasmssa.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
