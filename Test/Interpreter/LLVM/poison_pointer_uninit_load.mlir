// RUN: veir-interpret %s | filecheck %s

// A ptr value loaded from a stack-allocated pointer that was never written to
// is poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !llvm.ptr}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %p = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    "func.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
