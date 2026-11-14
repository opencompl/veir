"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %9 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %10 = "wasmssa.const"() <{value = 50 : i32}> : () -> i32
    %11 = "wasmssa.ne"(%9, %10) : (i32, i32) -> i32
    "wasmssa.return"(%11) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_1"}> ({
    %6 = "wasmssa.const"() <{value = 20 : i64}> : () -> i64
    %7 = "wasmssa.const"() <{value = 5 : i64}> : () -> i64
    %8 = "wasmssa.ne"(%6, %7) : (i64, i64) -> i32
    "wasmssa.return"(%8) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_2"}> ({
    %3 = "wasmssa.const"() <{value = 5.000000e+00 : f32}> : () -> f32
    %4 = "wasmssa.const"() <{value = 1.400000e+01 : f32}> : () -> f32
    %5 = "wasmssa.ne"(%3, %4) : (f32, f32) -> i32
    "wasmssa.return"(%5) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_3"}> ({
    %0 = "wasmssa.const"() <{value = 1.700000e+01 : f64}> : () -> f64
    %1 = "wasmssa.const"() <{value = 0.000000e+00 : f64}> : () -> f64
    %2 = "wasmssa.ne"(%0, %1) : (f64, f64) -> i32
    "wasmssa.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
