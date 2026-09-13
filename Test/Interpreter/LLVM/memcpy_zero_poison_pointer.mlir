// RUN: veir-interpret %s | filecheck %s

// A copy of no bytes reaches no memory, so it is allowed even through a
// poison pointer, the same rule that lets a zero-byte access go through a
// dangling one.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %poison = "llvm.mlir.poison"() : () -> i64
    %bad = "llvm.inttoptr"(%poison) : (i64) -> !llvm.ptr
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%p, %bad, %zero) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "func.return"(%one) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
