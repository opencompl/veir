// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<ptr (i64, i64)>, linkage = #llvm.linkage<external>, sym_name = "calloc"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %p = "llvm.call"(%two, %four) <{callee = @calloc, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (i64, i64) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
