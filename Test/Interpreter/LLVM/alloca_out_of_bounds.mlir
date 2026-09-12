// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %i = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %three = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %five = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p1 = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%five, %q) : (i32, !llvm.ptr) -> ()
    "llvm.store"(%three, %p1) : (i32, !llvm.ptr) -> ()
    %v = "llvm.load"(%q) : (!llvm.ptr) -> i32
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
