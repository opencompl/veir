// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %0 = "gmir.g_add"() : () -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_add: Expected 2 operand(s)
