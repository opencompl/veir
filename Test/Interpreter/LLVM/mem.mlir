// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i8, i8, i32, i16)}> ({
    %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %2 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
    %3 = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %4 = "llvm.alloca"(%1) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
    %5 = "llvm.alloca"(%1) <{ "elem_type" = i8 }> : (i64) -> !llvm.ptr
    "llvm.store"(%2, %4) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%3, %5) : (i8, !llvm.ptr) -> ()
    %6 = "llvm.load"(%4) : (!llvm.ptr) -> i64
    %7 = "llvm.load"(%4) : (!llvm.ptr) -> i8
    %8 = "llvm.load"(%5) : (!llvm.ptr) -> i8
    %9 = "llvm.load"(%4) : (!llvm.ptr) -> i32
    %10 = "llvm.load"(%4) : (!llvm.ptr) -> i16
    "func.return"(%6, %7, %8, %9, %10) : (i64, i8, i8, i32, i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64, 0x08#8, 0x05#8, 0x00000008#32, 0x0008#16]
