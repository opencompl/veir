"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_0"}> ({
    %3 = "wasmssa.const"() <{value = 1 : i32}> : () -> i32
    "wasmssa.return"(%3) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i64, sym_name = "func_1"}> ({
    %2 = "wasmssa.const"() <{value = 3 : i64}> : () -> i64
    "wasmssa.return"(%2) : (i64) -> ()
  }) : () -> ()
// TODO: uncomment when float support is added
//  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_2"}> ({
//    %1 = "wasmssa.const"() <{value = 4.000000e+00 : f32}> : () -> f32
//    "wasmssa.return"(%1) : (f32) -> ()
//  }) : () -> ()
//  "wasmssa.func"() <{functionType = () -> f64, sym_name = "func_3"}> ({
//    %0 = "wasmssa.const"() <{value = 9.000000e+00 : f64}> : () -> f64
//    "wasmssa.return"(%0) : (f64) -> ()
//  }) : () -> ()
}) : () -> ()
