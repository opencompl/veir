// RUN: veir-interpret %s | filecheck %s

// Writing past the end of an `alloca` is UB, even if there may be another
// alloca available.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %five = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%five, %past) : (i32, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
