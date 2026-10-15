// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i32):
  %result = "gmir.g_sext_inreg"(%a) <{sz = 32 : i64}> : (i32) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_sext_inreg: Expected 'sz' to be smaller than the operand width 32, but got 32
