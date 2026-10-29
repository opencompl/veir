// RUN: veir-opt %s -p='print-dataflow{sccp}' | filecheck %s

// gMIR folds whose result is poison. The gMIR materializer cannot represent
// poison, so these are only visible to the analysis.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "poison"}> ({
  ^entry(%x : i32):
    %zero = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
    %width = "gmir.g_constant"() <{value = 32 : i32}> : () -> i32
    %width_minus_one = "gmir.g_constant"() <{value = 31 : i32}> : () -> i32
    // Division by zero is UB.
    %udiv = "gmir.g_udiv"(%x, %zero) : (i32, i32) -> i32
    // CHECK: // dataflow.constant gmir.g_udiv result 0 = const(poison)
    // Shifting by the bit width or more is poison.
    %shl = "gmir.g_shl"(%x, %width) : (i32, i32) -> i32
    // CHECK: // dataflow.constant gmir.g_shl result 0 = const(poison)
    %in_range = "gmir.g_shl"(%x, %width_minus_one) : (i32, i32) -> i32
    // CHECK: // dataflow.constant gmir.g_shl result 0 = top
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
