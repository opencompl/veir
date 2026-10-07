// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: not veir-opt %s -p=isel-riscv64 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %q = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, 1, 0>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.getelementptr: type i64 cannot be indexed (index #2)
