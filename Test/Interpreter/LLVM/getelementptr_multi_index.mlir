// RUN: veir-interpret %s | filecheck %s

// `getelementptr`s with several indices, into a struct
// `{i8, [3 x [5 x i16]], i64}`: the array is at offset 2, and the i64 at 32.
// Dynamic operands include a negative i32 index.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %s = "llvm.alloca"(%one) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i16>>, i64)>}> : (i64) -> !llvm.ptr
    %i = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %j = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32

    // s.f1[2][4] = 0x1234, at 2 + 2 * 10 + 4 * 2 = 30
    %four = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %last = "llvm.getelementptr"(%s, %i, %four) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i16>>, i64)>, rawConstantIndices = array<i32: 0, 1, -2147483648, -2147483648>}> : (!llvm.ptr, i64, i32) -> !llvm.ptr
    %v1 = "llvm.mlir.constant"() <{value = 4660 : i16}> : () -> i16
    "llvm.store"(%v1, %last) : (i16, !llvm.ptr) -> ()

    // (&s.f1[2][4])[-1] = 0x56, at 28
    %prev = "llvm.getelementptr"(%last, %j) <{elem_type = i16, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    %v2 = "llvm.mlir.constant"() <{value = 86 : i16}> : () -> i16
    "llvm.store"(%v2, %prev) : (i16, !llvm.ptr) -> ()

    // s.f2 = 100, at byte offset 32
    %f2 = "llvm.getelementptr"(%s) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i16>>, i64)>, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    %v3 = "llvm.mlir.constant"() <{value = 100 : i64}> : () -> i64
    "llvm.store"(%v3, %f2) : (i64, !llvm.ptr) -> ()

    // Read back s.f1[2][3] (a dynamic index, then a constant one), s.f1[2][4]
    // and s.f2.
    %at28 = "llvm.getelementptr"(%s, %i) <{elem_type = !llvm.struct<(i8, !llvm.array<3 x !llvm.array<5 x i16>>, i64)>, rawConstantIndices = array<i32: 0, 1, -2147483648, 3>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %r1 = "llvm.load"(%at28) : (!llvm.ptr) -> i16
    %r2 = "llvm.load"(%last) : (!llvm.ptr) -> i16
    %r3 = "llvm.load"(%f2) : (!llvm.ptr) -> i64
    %r1w = "llvm.zext"(%r1) : (i16) -> i64
    %r2w = "llvm.zext"(%r2) : (i16) -> i64
    %sum1 = "llvm.add"(%r1w, %r2w) : (i64, i64) -> i64
    %sum = "llvm.add"(%sum1, %r3) : (i64, i64) -> i64
    "llvm.return"(%sum) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// 0x56 + 0x1234 + 100 = 0x12ee
// CHECK: Program output: #[0x00000000000012ee#64]
