"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> i32, sym_name = "i32.reinterpret_f32"}> ({
    %6 = "wasmssa.const"() <{value = -1.000000e+00 : f32}> : () -> f32
    %7 = "wasmssa.reinterpret"(%6) : (f32) -> i32
    "wasmssa.return"(%7) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> i64, sym_name = "i64.reinterpret_f64"}> ({
    %4 = "wasmssa.const"() <{value = -1.000000e+00 : f64}> : () -> f64
    %5 = "wasmssa.reinterpret"(%4) : (f64) -> i64
    "wasmssa.return"(%5) : (i64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "f32.reinterpret_i32"}> ({
    %2 = "wasmssa.const"() <{value = -1 : i32}> : () -> i32
    %3 = "wasmssa.reinterpret"(%2) : (i32) -> f32
    "wasmssa.return"(%3) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "f64.reinterpret_i64"}> ({
    %0 = "wasmssa.const"() <{value = -1 : i64}> : () -> i64
    %1 = "wasmssa.reinterpret"(%0) : (i64) -> f64
    "wasmssa.return"(%1) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
