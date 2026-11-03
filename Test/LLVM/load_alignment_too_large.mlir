// RUN: not veir-opt %s 2>&1 | filecheck %s

// LLVM's largest alignment is 2^32. MLIR accepts a larger one, so there is no
// MLIR_INVALID line; VeIR rejects it, as LLVM would.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %v = "llvm.load"(%p) <{alignment = 8589934592 : i64}> : (!llvm.ptr) -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.load: alignment attribute exceeds the largest alignment LLVM supports, 2^32
