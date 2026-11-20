// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i65):
  %lo, %hi = "gmir.g_unmerge_values"(%a) : (i65) -> (i32, i32)
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_unmerge_values: Expected the results to be 65 bits wide in total, but got 64
