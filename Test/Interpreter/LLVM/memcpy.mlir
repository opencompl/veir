// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// LLUBI: cannot cross-check this test: llubi gives a load of uninitialized
// memory an arbitrary concrete value rather than poison.

// `llvm.intr.memcpy` copies bytes along with their poison bits. A copied
// pointer still points to its object.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i32, i32, i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %val = "llvm.mlir.constant"() <{value = 72623859790382856 : i64}> : () -> i64
    %half = "llvm.mlir.constant"() <{value = 287454020 : i32}> : () -> i32
    %src = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %dst = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%val, %src) : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%dst, %src, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    %copy = "llvm.load"(%dst) : (!llvm.ptr) -> i64
    %part = "llvm.alloca"(%two) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%half, %part) : (i32, !llvm.ptr) -> ()
    %dst2 = "llvm.alloca"(%two) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%dst2, %part, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    %lo = "llvm.load"(%dst2) : (!llvm.ptr) -> i32
    %dst2hi = "llvm.getelementptr"(%dst2, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %hi = "llvm.load"(%dst2hi) : (!llvm.ptr) -> i32
    %pp = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %pp2 = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%src, %pp) : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%pp2, %pp, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    %p = "llvm.load"(%pp2) : (!llvm.ptr) -> !llvm.ptr
    %through = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%copy, %lo, %hi, %through) : (i64, i32, i32, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0102030405060708#64, 0x11223344#32, poison, 0x0102030405060708#64]
