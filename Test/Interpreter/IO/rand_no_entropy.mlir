// RUN: veir-interpret %s | filecheck %s

// The interpreter starts with an empty entropy source, so `io.rand` is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %n = "io.rand"(%buf, %len) : (!llvm.ptr, i64) -> i64
    // CHECK: Undefined behavior
    "func.return"(%n) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
