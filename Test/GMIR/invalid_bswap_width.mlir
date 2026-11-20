// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i8):
  %r = "gmir.g_bswap"(%a) : (i8) -> i8
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_bswap: bitwidth must be 16, 32, or 64
