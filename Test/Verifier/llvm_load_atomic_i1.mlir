// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// An atomic access needs a power-of-two size of at least 8 bits.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %0 = "llvm.load"(%p) <{alignment = 1 : i64, ordering = 2 : i64}> : (!llvm.ptr) -> i1
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: 'llvm.load' op unsupported type i1 for atomic access
