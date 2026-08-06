// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// From sqlite3.c sqlite3DigitPairs (L37381).

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 2 : i64, constant, dso_local, global_type = !llvm.struct<(array<201 x i8>, i8)>, linkage = #llvm.linkage<internal>, sym_name = "digitPairs", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = "00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899\00"}> : () -> !llvm.array<201 x i8>
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

// CHECK: "value" = "00010203
