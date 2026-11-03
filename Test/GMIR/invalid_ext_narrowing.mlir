// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i64):
  %result = "gmir.g_zext"(%a) : (i64) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_zext: Operand's width must be smaller than result's width
