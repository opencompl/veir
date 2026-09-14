// RUN: veir-interpret %s | filecheck %s

// A poison pointer written to memory and read back gives poison again.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !llvm.ptr}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %dst = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%p, %dst) : (!llvm.ptr, !llvm.ptr) -> ()
    %back = "llvm.load"(%dst) : (!llvm.ptr) -> !llvm.ptr
    "func.return"(%back) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
