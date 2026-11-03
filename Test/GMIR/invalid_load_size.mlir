// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr):
  %r = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_load: Expected 'size' to be at most the value width 32, but got 64
