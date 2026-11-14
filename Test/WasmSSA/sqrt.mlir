"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "sqrt_f32"}> ({
    %2 = "wasmssa.const"() <{value = 1.000000e+01 : f32}> : () -> f32
    %3 = "wasmssa.sqrt"(%2) : (f32) -> f32
    "wasmssa.return"(%3) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "sqrt_f64"}> ({
    %0 = "wasmssa.const"() <{value = 1.000000e+01 : f64}> : () -> f64
    %1 = "wasmssa.sqrt"(%0) : (f64) -> f64
    "wasmssa.return"(%1) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
