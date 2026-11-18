// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir > %t
// RUN: filecheck %s --input-file=%t --check-prefix=GMIR
// RUN: veir-interpret %t | filecheck %s

// The translated GEPs compute the same addresses. The indices are loaded, so
// they are not constants: `j` is the `i32` 2, which is sign-extended, and `n` is the `i64` -1.
// `p[2][-1]` is `p[1]`, which holds 1, and `p[0][j]` is `p[2]`, which holds 2.

// CHECK: Program output: #[0x0001#16, 0x0002#16]

// GMIR:     "gmir.g_sext"
// GMIR:     "gmir.g_ptr_add"
// GMIR-NOT: llvm.getelementptr

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i16, i16)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = !llvm.array<4 x i16>}> : (i64) -> !llvm.ptr
    %js = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %ns = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %two32 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %minus1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    "llvm.store"(%two32, %js) : (i32, !llvm.ptr) -> ()
    "llvm.store"(%minus1, %ns) : (i64, !llvm.ptr) -> ()
    %j = "llvm.load"(%js) : (!llvm.ptr) -> i32
    %n = "llvm.load"(%ns) : (!llvm.ptr) -> i64
    %v1 = "llvm.mlir.constant"() <{value = 1 : i16}> : () -> i16
    %v2 = "llvm.mlir.constant"() <{value = 2 : i16}> : () -> i16
    %p1 = "llvm.getelementptr"(%p, %one) <{elem_type = i16, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v1, %p1) : (i16, !llvm.ptr) -> ()
    %p2 = "llvm.getelementptr"(%p, %j) <{elem_type = i16, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.store"(%v2, %p2) : (i16, !llvm.ptr) -> ()
    %back = "llvm.getelementptr"(%p2, %n) <{elem_type = i16, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %x = "llvm.load"(%back) : (!llvm.ptr) -> i16
    %row = "llvm.getelementptr"(%p, %j) <{elem_type = !llvm.array<4 x i16>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    %y = "llvm.load"(%row) : (!llvm.ptr) -> i16
    "func.return"(%x, %y) : (i16, i16) -> ()
  }) : () -> ()
}) : () -> ()
