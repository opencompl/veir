"builtin.module"() ({
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "convert_i32_u_to_f32"}> ({
    %14 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %15 = "wasmssa.convert_u"(%14) : (i32) -> f32
    "wasmssa.return"(%15) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "convert_i32_s_to_f32"}> ({
    %12 = "wasmssa.const"() <{value = 42 : i32}> : () -> i32
    %13 = "wasmssa.convert_s"(%12) : (i32) -> f32
    "wasmssa.return"(%13) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "convert_i64_u_to_f32"}> ({
    %10 = "wasmssa.const"() <{value = 17 : i64}> : () -> i64
    %11 = "wasmssa.convert_u"(%10) : (i64) -> f32
    "wasmssa.return"(%11) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f32, sym_name = "convert_i64s_to_f32"}> ({
    %8 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %9 = "wasmssa.convert_s"(%8) : (i64) -> f32
    "wasmssa.return"(%9) : (f32) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "convert_i32_u_to_f64"}> ({
    %6 = "wasmssa.const"() <{value = 10 : i32}> : () -> i32
    %7 = "wasmssa.convert_u"(%6) : (i32) -> f64
    "wasmssa.return"(%7) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "convert_i32_s_to_f64"}> ({
    %4 = "wasmssa.const"() <{value = 42 : i32}> : () -> i32
    %5 = "wasmssa.convert_s"(%4) : (i32) -> f64
    "wasmssa.return"(%5) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "convert_i64_u_to_f64"}> ({
    %2 = "wasmssa.const"() <{value = 17 : i64}> : () -> i64
    %3 = "wasmssa.convert_u"(%2) : (i64) -> f64
    "wasmssa.return"(%3) : (f64) -> ()
  }) : () -> ()
  "wasmssa.func"() <{exported, functionType = () -> f64, sym_name = "convert_i64s_to_f64"}> ({
    %0 = "wasmssa.const"() <{value = 10 : i64}> : () -> i64
    %1 = "wasmssa.convert_s"(%0) : (i64) -> f64
    "wasmssa.return"(%1) : (f64) -> ()
  }) : () -> ()
}) : () -> ()
