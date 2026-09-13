// RUN: veir-interpret %s | filecheck %s

// An access of no bytes is allowed even through a dangling pointer.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64)>, linkage = #llvm.linkage<external>, sym_name = "malloc"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "free"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %p = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    %q = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) <{callee = @free, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%q, %p, %zero) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "func.return"(%one) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
