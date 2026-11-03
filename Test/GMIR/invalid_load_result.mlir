// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr):
  %r = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> !llvm.byte<8>
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_load: Expected result to have integer or !llvm.ptr type
