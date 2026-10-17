// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr, i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %v: i32):
    "llvm.store"(%v, %p) <{alignment = 4 : i64, ordering = 2 : i32}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.store: expected 'ordering' to be an i64 integer attribute, but got 2 : i32
