// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// 3 is not an ordering at all: MLIR leaves that number unused.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %0 = "llvm.load"(%p) <{alignment = 4 : i64, ordering = 3 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.load: invalid ordering 3
