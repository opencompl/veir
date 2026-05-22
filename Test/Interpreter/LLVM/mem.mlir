// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %2 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
    %3 = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %4 = "llvm.alloca"(%1) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
    %5 = "llvm.alloca"(%1) <{ "elem_type" = i8 }> : (i64) -> !llvm.ptr
    "llvm.store"(%4, %2) : (!llvm.ptr, i64) -> ()
    "llvm.store"(%5, %3) : (!llvm.ptr, i8) -> ()
    %6 = "llvm.load"(%4) : (!llvm.ptr) -> i64
    %7 = "llvm.load"(%4) : (!llvm.ptr) -> i8
    %8 = "llvm.load"(%5) : (!llvm.ptr) -> i8
    "func.return"(%6, %7, %8) : (i64, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64, 0x08#8, 0x05#8]
