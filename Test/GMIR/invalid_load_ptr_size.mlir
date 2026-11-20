// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr):
  %r = "gmir.g_load"(%p) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> !llvm.ptr
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_load: Expected 'size' to be the pointer width 64, but got 32
