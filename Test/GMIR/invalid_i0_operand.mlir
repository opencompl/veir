// RUN: not veir-opt %s 2>&1 | filecheck %s

// `i0` is not an LLVM type, so no `gmir` operation accepts an `i0` operand.
"builtin.module"() ({
^bb0(%a: i0):
  %r = "gmir.g_zext"(%a) : (i0) -> i64
}) : () -> ()

// CHECK: gmir.g_zext: operand 0 has forbidden i0 type
