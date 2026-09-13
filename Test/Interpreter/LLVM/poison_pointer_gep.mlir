// RUN: veir-interpret %s | filecheck %s

// Offsetting a poison pointer gives a poison pointer.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !llvm.ptr}> ({
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "func.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
