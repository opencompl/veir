// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64)>, linkage = #llvm.linkage<external>, sym_name = "malloc"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, linkage = #llvm.linkage<external>, sym_name = "free"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %i = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %j = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %three = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %five = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %p = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    %q = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    %p1 = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %q1 = "llvm.getelementptr"(%q, %j) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%three, %p1) : (i32, !llvm.ptr) -> ()
    "llvm.store"(%five, %q1) : (i32, !llvm.ptr) -> ()
    "llvm.call"(%p) <{callee = @free, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> ()
    %v = "llvm.load"(%p1) : (!llvm.ptr) -> i32
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
