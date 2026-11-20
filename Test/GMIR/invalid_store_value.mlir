// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%v: !llvm.byte<64>, %p: !llvm.ptr):
  "gmir.g_store"(%v, %p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.byte<64>, !llvm.ptr) -> ()
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_store: Expected operand 0 to have integer or !llvm.ptr type
