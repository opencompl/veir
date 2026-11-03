// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 2 : i64, constant, dso_local, global_type = !llvm.array<201 x i32>, linkage = #llvm.linkage<internal>, sym_name = "digitPairs", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = "00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899\00"}> : () -> !llvm.array<201 x i32>
    "llvm.return"(%0) : (!llvm.array<201 x i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: Expected array<N x i8> result type for a string constant

