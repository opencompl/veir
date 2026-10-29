// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i8, %b: i8):
  %sum, %carry = "gmir.g_uaddo"(%a, %b) : (i8, i8) -> (i8, i8)
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_uaddo: Expected the carry to have type i1, but got i8
