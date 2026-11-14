"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> f64, sym_name = "func_0"}> ({
    %0 = "wasmssa.const"() <{value = 1.050000e+01 : f32}> : () -> f32
    %1 = "wasmssa.promote"(%0) : (f32) -> f64
    "wasmssa.return"(%1) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
