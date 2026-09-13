// RUN: veir-interpret %s | filecheck %s

// `realloc` moves the bytes to a fresh object and frees the old one, so the
// value survives and the old pointer dangles.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64)>, linkage = #llvm.linkage<external>, sym_name = "malloc"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<ptr (ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "realloc"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %sixteen = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %p = "llvm.call"(%eight) <{callee = @malloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %q = "llvm.call"(%p, %sixteen) <{callee = @realloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64]
