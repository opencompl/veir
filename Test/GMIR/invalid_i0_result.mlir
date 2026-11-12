// RUN: not veir-opt %s 2>&1 | filecheck %s

// `i0` is not an LLVM type, so no `gmir` operation produces an `i0` result.
"builtin.module"() ({
^bb0(%a: i64):
  %r = "gmir.g_trunc"(%a) : (i64) -> i0
}) : () -> ()

// CHECK: gmir.g_trunc: result 0 has forbidden i0 type
