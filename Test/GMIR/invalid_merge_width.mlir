// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i64, %b: i64):
  %result = "gmir.g_merge_values"(%a, %b) : (i64, i64) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_merge_values: Expected the results to be 128 bits wide in total, but got 64
