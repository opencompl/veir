// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  ^bb0(%lhs: i32, %rhs: i16):
    %0 = "gmir.g_add"(%lhs, %rhs) : (i32, i16) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_add: type mismatch: expected i32, got i16
