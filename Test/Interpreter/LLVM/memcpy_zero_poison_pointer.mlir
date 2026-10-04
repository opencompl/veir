// RUN: veir-interpret %s | filecheck %s

// A copy of no bytes reaches no memory, so it is allowed even through a
// poison pointer, the same rule that lets a zero-byte access go through a
// dangling one.

// The cross-checks cannot read this test: the translator has no
// `llvm.intr.memcpy`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %bad = "llvm.mlir.poison"() : () -> !llvm.ptr
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%p, %bad, %zero) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"(%one) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
