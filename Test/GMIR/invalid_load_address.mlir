// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%a: i64):
  %r = "gmir.g_load"(%a) <{alignment = 8 : i64, size = 64 : i64}> : (i64) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_load: Expected operand 0 to have !llvm.ptr type
