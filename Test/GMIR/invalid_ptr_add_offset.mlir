// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%p: !llvm.ptr, %a: i32):
  %r = "gmir.g_ptr_add"(%p, %a) : (!llvm.ptr, i32) -> !llvm.ptr
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_ptr_add: Expected operand 1 to have type i64, but got i32
