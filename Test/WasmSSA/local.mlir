"builtin.module"() ({
  "wasmssa.func"() <{functionType = () -> f32, sym_name = "func_0"}> ({
    %9 = "wasmssa.local"() <{type = f32}> : () -> !wasmssa<local ref to f32>
    %10 = "wasmssa.local"() <{type = f32}> : () -> !wasmssa<local ref to f32>
    %11 = "wasmssa.const"() <{value = 8.000000e+00 : f32}> : () -> f32
    "wasmssa.local_set"(%9, %11) : (!wasmssa<local ref to f32>, f32) -> ()
    %12 = "wasmssa.local_get"(%9) : (!wasmssa<local ref to f32>) -> f32
    %13 = "wasmssa.const"() <{value = 1.200000e+01 : f32}> : () -> f32
    %14 = "wasmssa.local_tee"(%10, %13) : (!wasmssa<local ref to f32>, f32) -> f32
    %15 = "wasmssa.add"(%12, %14) : (f32, f32) -> f32
    "wasmssa.return"(%15) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = () -> i32, sym_name = "func_1"}> ({
    %2 = "wasmssa.local"() <{type = i32}> : () -> !wasmssa<local ref to i32>
    %3 = "wasmssa.local"() <{type = i32}> : () -> !wasmssa<local ref to i32>
    %4 = "wasmssa.const"() <{value = 8 : i32}> : () -> i32
    "wasmssa.local_set"(%2, %4) : (!wasmssa<local ref to i32>, i32) -> ()
    %5 = "wasmssa.local_get"(%2) : (!wasmssa<local ref to i32>) -> i32
    %6 = "wasmssa.const"() <{value = 12 : i32}> : () -> i32
    %7 = "wasmssa.local_tee"(%3, %6) : (!wasmssa<local ref to i32>, i32) -> i32
    %8 = "wasmssa.add"(%5, %7) : (i32, i32) -> i32
    "wasmssa.return"(%8) : (i32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{functionType = (i32) -> i32, sym_name = "func_2"}> ({
  ^bb0(%arg0: !wasmssa<local ref to i32>):
    %0 = "wasmssa.const"() <{value = 3 : i32}> : () -> i32
    "wasmssa.local_set"(%arg0, %0) : (!wasmssa<local ref to i32>, i32) -> ()
    %1 = "wasmssa.local_get"(%arg0) : (!wasmssa<local ref to i32>) -> i32
    "wasmssa.return"(%1) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
