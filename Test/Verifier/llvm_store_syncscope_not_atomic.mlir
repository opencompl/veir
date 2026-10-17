// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `syncscope` only means something for an atomic access.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr, i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %v: i32):
    "llvm.store"(%v, %p) <{alignment = 4 : i64, syncscope = "singlethread"}> : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: 'llvm.store' op expected syncscope to be null for non-atomic access
