// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %q = "llvm.getelementptr"(%p) <{elem_type = i8, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.getelementptr: Expected the result to have !llvm.ptr type
