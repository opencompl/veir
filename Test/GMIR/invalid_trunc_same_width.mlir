// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i32):
  %result = "gmir.g_trunc"(%a) : (i32) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_trunc: Result's width must be smaller than operand's width
