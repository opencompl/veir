// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %index = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %q = "llvm.getelementptr"(%p, %index) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.getelementptr: expected index 1 indexing a struct to be constant
