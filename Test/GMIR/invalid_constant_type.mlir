// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %result = "gmir.g_constant"() <{value = 1 : i32}> : () -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_constant: Expected result type to be equal to the constant's type
