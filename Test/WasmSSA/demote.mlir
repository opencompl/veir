"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_0"}> ({
    %0 = "wasmssa.const"() <{value = 2.240000e+00 : f64}> : () -> f64
    %1 = "wasmssa.demote"(%0) : (f64) -> f32
    "wasmssa.return"(%1) : (f32) -> ()
  }) : () -> ()
}) : () -> ()
