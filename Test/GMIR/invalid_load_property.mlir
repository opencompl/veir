// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr):
  %r = "gmir.g_load"(%p) <{alignment = 4 : i64, invariantGroup, size = 32 : i64}> : (!llvm.ptr) -> i32
}) : () -> ()

// CHECK: error: gmir.g_load: unexpected property 'invariantGroup'
