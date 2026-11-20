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
  // Nested aggregate updates preserve earlier SSA values.
  "llvm.mlir.global"() <{global_type = !llvm.struct<packed (array<2 x i32>, ptr)>, linkage = #llvm.linkage<external>, sym_name = "record"}> ({
    %base = "llvm.mlir.zero"() : () -> !llvm.struct<packed (array<2 x i32>, ptr)>
    %p = "llvm.mlir.addressof"() <{global_name = @data}> : () -> !llvm.ptr
    %a = "llvm.mlir.constant"() <{value = dense<[5, 6]> : tensor<2xi32>}> : () -> !llvm.array<2 x i32>
    %nine = "llvm.mlir.constant"() <{value = 9 : i32}> : () -> i32
    %r1 = "llvm.insertvalue"(%base, %p) <{position = array<i64: 1>}> : (!llvm.struct<packed (array<2 x i32>, ptr)>, !llvm.ptr) -> !llvm.struct<packed (array<2 x i32>, ptr)>
    %r2 = "llvm.insertvalue"(%r1, %a) <{position = array<i64: 0>}> : (!llvm.struct<packed (array<2 x i32>, ptr)>, !llvm.array<2 x i32>) -> !llvm.struct<packed (array<2 x i32>, ptr)>
    %r3 = "llvm.insertvalue"(%r2, %nine) <{position = array<i64: 0, 1>}> : (!llvm.struct<packed (array<2 x i32>, ptr)>, i32) -> !llvm.struct<packed (array<2 x i32>, ptr)>
    %old = "llvm.extractvalue"(%r2) <{position = array<i64: 0, 1>}> : (!llvm.struct<packed (array<2 x i32>, ptr)>) -> i32
    %r4 = "llvm.insertvalue"(%r3, %old) <{position = array<i64: 0, 0>}> : (!llvm.struct<packed (array<2 x i32>, ptr)>, i32) -> !llvm.struct<packed (array<2 x i32>, ptr)>
    "llvm.return"(%r4) : (!llvm.struct<packed (array<2 x i32>, ptr)>) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "stub"}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: @interior = global ptr inttoptr (i64 add (i64 ptrtoint (ptr getelementptr inbounds ([4 x i32], ptr @data, i32 0, i64 2) to i64), i64 4) to ptr)
// CHECK: @record = global <{ [2 x i32], ptr }> <{ [2 x i32] [i32 6, i32 9], ptr @data }>
