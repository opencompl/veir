// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i64)>, sym_name = "f"}> ({
  ^bb0(%base: i64):
    %result = "llvm.getelementptr"(%base) <{elem_type = i8, rawConstantIndices = array<i32: 0>}> : (i64) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.getelementptr: Expected operand 0 to have !llvm.ptr type
