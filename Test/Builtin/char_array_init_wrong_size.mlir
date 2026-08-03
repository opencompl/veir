// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 2 : i64, constant, dso_local, global_type = !llvm.struct<(array<201 x i8>, i8)>, linkage = #llvm.linkage<internal>, sym_name = "digitPairs", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = "00\00"}> : () -> !llvm.array<201 x i8>
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<(array<201 x i8>, i8)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<(array<201 x i8>, i8)>, !llvm.array<201 x i8>) -> !llvm.struct<(array<201 x i8>, i8)>
    %4 = "llvm.insertvalue"(%3, %0) <{position = array<i64: 1>}> : (!llvm.struct<(array<201 x i8>, i8)>, i8) -> !llvm.struct<(array<201 x i8>, i8)>
    "llvm.return"(%4) : (!llvm.struct<(array<201 x i8>, i8)>) -> ()
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<!llvm.ptr ()>, linkage = #llvm.linkage<external>, sym_name = "getDigitPairs", visibility_ = 0 : i64}> ({
    %5 = "llvm.mlir.addressof"() <{global_name = @digitPairs}> : () -> !llvm.ptr
    "llvm.return"(%5) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: string length 3 does not match declared array size 201
