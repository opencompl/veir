// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr):
  %r = "gmir.g_load"(%p) <{alignment = 0 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_load: Expected 'alignment' to be a power of two, but got 0
