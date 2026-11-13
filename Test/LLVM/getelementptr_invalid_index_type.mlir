// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A dynamic index of a `getelementptr` is an integer.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, sym_name = "f"}> ({
  ^bb0(%base: !llvm.ptr):
    %result = "llvm.getelementptr"(%base, %base) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.getelementptr: Expected operand 1 to have integer type
