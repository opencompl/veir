// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i32, %b: i64):
  %r = "gmir.g_mul"(%a, %b) : (i32, i64) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_mul: type mismatch
