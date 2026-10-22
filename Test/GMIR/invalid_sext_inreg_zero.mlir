// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i64):
  %result = "gmir.g_sext_inreg"(%a) <{sz = 0 : i64}> : (i64) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_sext_inreg: Expected 'sz' to be at least 1, but got 0
