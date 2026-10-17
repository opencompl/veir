// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// An atomic access needs a power-of-two size of at least 8 bits.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr, i24)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %v: i24):
    "llvm.store"(%v, %p) <{alignment = 4 : i64, ordering = 2 : i64}> : (i24, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: 'llvm.store' op unsupported type i24 for atomic access
