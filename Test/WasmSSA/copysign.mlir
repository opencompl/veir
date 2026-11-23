"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "copysign_f32"}> ({
    %3 = "wasmssa.const"() <{value = 1.000000e+01 : f32}> : () -> f32
    %4 = "wasmssa.const"() <{value = 1.000000e+00 : f32}> : () -> f32
    %5 = "wasmssa.copysign"(%3, %4) : (f32, f32) -> f32
    "wasmssa.return"(%5) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "copysign_f64"}> ({
    %0 = "wasmssa.const"() <{value = 1.000000e+01 : f64}> : () -> f64
    %1 = "wasmssa.const"() <{value = 1.000000e+00 : f64}> : () -> f64
    %2 = "wasmssa.copysign"(%0, %1) : (f64, f64) -> f64
    "wasmssa.return"(%2) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
