// RUN: veir-interpret %s | filecheck %s

// `inttoptr` of a poison integer is a poison pointer, and offsetting it
// leaves it poison rather than making the program undefined.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %poison = "llvm.mlir.poison"() : () -> i64
    %p = "llvm.inttoptr"(%poison) : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "llvm.ptrtoint"(%q) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
