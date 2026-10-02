// RUN: veir-interpret %s | filecheck %s

// `llvm.intr.memmove` copies correctly when the ranges overlap, in either
// direction.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %val = "llvm.mlir.constant"() <{value = 72623859790382856 : i64}> : () -> i64
    %buf = "llvm.alloca"(%two) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %buf1 = "llvm.getelementptr"(%buf, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%val, %buf) : (i64, !llvm.ptr) -> ()
    "llvm.intr.memmove"(%buf1, %buf, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %up = "llvm.load"(%buf1) : (!llvm.ptr) -> i64
    "llvm.intr.memmove"(%buf, %buf1, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %down = "llvm.load"(%buf) : (!llvm.ptr) -> i64
    "func.return"(%up, %down) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0102030405060708#64, 0x0102030405060708#64]
