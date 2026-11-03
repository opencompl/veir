// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = !llvm.array<4 x i32>, linkage = #llvm.linkage<external>, sym_name = "data", value = dense<[10, 20, 30, 40]> : tensor<4xi32>}> ({}) : () -> ()
  // Mixed inline/SSA indices, followed by symbolic pointer arithmetic.
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "interior"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @data}> : () -> !llvm.ptr
    %i = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %q = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<4 x i32>, rawConstantIndices = array<i32: 0, -2147483648>, noWrapFlags = 3 : i32}> : (!llvm.ptr, i64) -> !llvm.ptr
    %n = "llvm.ptrtoint"(%q) : (!llvm.ptr) -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %sum = "llvm.add"(%n, %four) : (i64, i64) -> i64
    %r = "llvm.inttoptr"(%sum) : (i64) -> !llvm.ptr
    "llvm.return"(%r) : (!llvm.ptr) -> ()
  }) : () -> ()
  // Nested packed layout, pointer relocation, and repeated array updates.
  "llvm.mlir.global"() <{global_type = !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>, linkage = #llvm.linkage<external>, sym_name = "record"}> ({
    %base = "llvm.mlir.zero"() : () -> !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>
    %p = "llvm.mlir.addressof"() <{global_name = @data}> : () -> !llvm.ptr
    %a = "llvm.mlir.constant"() <{value = dense<[5, 6]> : tensor<2xi32>}> : () -> !llvm.array<2 x i32>
    %nine = "llvm.mlir.constant"() <{value = 9 : i32}> : () -> i32
    %r1 = "llvm.insertvalue"(%base, %p) <{position = array<i64: 1, 1>}> : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>, !llvm.ptr) -> !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>
    %r2 = "llvm.insertvalue"(%r1, %a) <{position = array<i64: 2>}> : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>, !llvm.array<2 x i32>) -> !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>
    %r3 = "llvm.insertvalue"(%r2, %nine) <{position = array<i64: 2, 1>}> : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>, i32) -> !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>
    %old = "llvm.extractvalue"(%r2) <{position = array<i64: 2, 1>}> : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>) -> i32
    %r4 = "llvm.insertvalue"(%r3, %old) <{position = array<i64: 2, 0>}> : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>, i32) -> !llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>
    "llvm.return"(%r4) : (!llvm.struct<(i8, struct<packed (i16, ptr)>, array<2 x i32>)>) -> ()
  }) : () -> ()
  // Untouched undef and poison elements survive insertion; strings can be extracted.
  "llvm.mlir.global"() <{global_type = !llvm.array<2 x !llvm.array<2 x i8>>, linkage = #llvm.linkage<external>, sym_name = "partial"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.array<2 x !llvm.array<2 x i8>>
    %p = "llvm.mlir.poison"() : () -> !llvm.array<2 x i8>
    %s = "llvm.mlir.constant"() <{value = "hi"}> : () -> !llvm.array<2 x i8>
    %c = "llvm.extractvalue"(%s) <{position = array<i64: 1>}> : (!llvm.array<2 x i8>) -> i8
    %a = "llvm.insertvalue"(%p, %c) <{position = array<i64: 0>}> : (!llvm.array<2 x i8>, i8) -> !llvm.array<2 x i8>
    %r = "llvm.insertvalue"(%u, %a) <{position = array<i64: 1>}> : (!llvm.array<2 x !llvm.array<2 x i8>>, !llvm.array<2 x i8>) -> !llvm.array<2 x !llvm.array<2 x i8>>
    "llvm.return"(%r) : (!llvm.array<2 x !llvm.array<2 x i8>>) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "read"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @interior}> : () -> !llvm.ptr
    %q = "llvm.load"(%p) : (!llvm.ptr) -> !llvm.ptr
    %v = "llvm.load"(%q) : (!llvm.ptr) -> i32
    %r = "llvm.zext"(%v) : (i32) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: @interior = global ptr inttoptr (i64 add (i64 ptrtoint (ptr getelementptr inbounds ([4 x i32], ptr @data, i32 0, i64 2) to i64), i64 4) to ptr)
// CHECK: @record = global { i8, <{ i16, ptr }>, [2 x i32] } { i8 zeroinitializer, <{ i16, ptr }> <{ i16 zeroinitializer, ptr @data }>, [2 x i32] [i32 6, i32 9] }
// CHECK: @partial = global [2 x [2 x i8]] [[2 x i8] undef, [2 x i8] [i8 105, i8 poison]]
// CHECK-LABEL: name: read
