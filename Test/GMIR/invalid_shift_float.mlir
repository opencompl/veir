// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: f32, %b: i32):
  %r = "gmir.g_shl"(%a, %b) : (f32, i32) -> f32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_shl: Expected operand 0 to have integer type
