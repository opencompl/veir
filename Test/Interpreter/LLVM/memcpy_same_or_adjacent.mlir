// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// `llvm.intr.memcpy` is defined when `dst` and `src` are the same pointer, or
// when the two ranges are adjacent in the same object.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %val = "llvm.mlir.constant"() <{value = 72623859790382856 : i64}> : () -> i64
    %buf = "llvm.alloca"(%two) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%val, %buf) : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%buf, %buf, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %same = "llvm.load"(%buf) : (!llvm.ptr) -> i64
    %buf8 = "llvm.getelementptr"(%buf, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%buf8, %buf, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %next = "llvm.load"(%buf8) : (!llvm.ptr) -> i64
    "func.return"(%same, %next) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0102030405060708#64, 0x0102030405060708#64]
