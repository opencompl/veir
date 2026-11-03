// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%v: i32, %p: !llvm.ptr):
  "gmir.g_store"(%v, %p) <{alignment = 4 : i64, size = 12 : i64}> : (i32, !llvm.ptr) -> ()
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_store: Expected 'size' to be a positive multiple of 8, but got 12
