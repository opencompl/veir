// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i32):
  %r = "gmir.g_bitcast"(%a) : (i32) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_bitcast: Expected operand and result to have the same bitwidth
