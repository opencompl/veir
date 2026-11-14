"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> f64, sym_name = "func_0"}> ({
    %10 = "wasmssa.const"() <{value = -1.210000e+01 : f64}> : () -> f64
    %11 = "wasmssa.ceil"(%10) : (f64) -> f64
    "wasmssa.return"(%11) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_1"}> ({
    %8 = "wasmssa.const"() <{value = 1.618000e+00 : f32}> : () -> f32
    %9 = "wasmssa.ceil"(%8) : (f32) -> f32
    "wasmssa.return"(%9) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> f64, sym_name = "func_2"}> ({
    %6 = "wasmssa.const"() <{value = -1.210000e+01 : f64}> : () -> f64
    %7 = "wasmssa.floor"(%6) : (f64) -> f64
    "wasmssa.return"(%7) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_3"}> ({
    %4 = "wasmssa.const"() <{value = 1.618000e+00 : f32}> : () -> f32
    %5 = "wasmssa.floor"(%4) : (f32) -> f32
    "wasmssa.return"(%5) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> f64, sym_name = "func_4"}> ({
    %2 = "wasmssa.const"() <{value = -1.210000e+01 : f64}> : () -> f64
    %3 = "wasmssa.trunc"(%2) : (f64) -> f64
    "wasmssa.return"(%3) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_5"}> ({
    %0 = "wasmssa.const"() <{value = 1.618000e+00 : f32}> : () -> f32
    %1 = "wasmssa.trunc"(%0) : (f32) -> f32
    "wasmssa.return"(%1) : (f32) -> ()
  }) : () -> ()
}) : () -> ()
