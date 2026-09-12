// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64)>, linkage = #llvm.linkage<external>, sym_name = "malloc"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "free"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %p = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) <{callee = @free, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @free, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    "func.return"(%zero) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
