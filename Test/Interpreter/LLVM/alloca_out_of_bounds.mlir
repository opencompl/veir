// RUN: veir-interpret %s | filecheck %s

// Storing past the end of an `alloca` is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p1 = "llvm.getelementptr"(%p, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%eight, %p1) : (i64, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
