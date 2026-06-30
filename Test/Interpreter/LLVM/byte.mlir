// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<64>, i32, i32)}> ({
    %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %2 = "llvm.mlir.constant"() <{ "value" = 17 : i64 }> : () -> i64
    %3 = "llvm.mlir.poison"() : () -> i8
    %4 = "llvm.alloca"(%1) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
    %5 = "llvm.mlir.constant"() <{ "value" = 4 : i64 }> : () -> i64
    %6 = "llvm.getelementptr"(%4, %5) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%2, %4) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%3, %6) : (i8, !llvm.ptr) -> ()
    %7 = "llvm.load"(%4) : (!llvm.ptr) -> !llvm.byte<64>
    %8 = "llvm.mlir.constant"() <{ "value" = 32 : i64 }> : () -> i64
    %9 = "llvm.lshr"(%7, %8) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %10 = "llvm.trunc"(%9) : (!llvm.byte<64>) -> !llvm.byte<32>
    %11 = "llvm.trunc"(%7) : (!llvm.byte<64>) -> !llvm.byte<32>
    %12 = "llvm.bitcast"(%10) : (!llvm.byte<32>) -> i32
    %13 = "llvm.bitcast"(%11) : (!llvm.byte<32>) -> i32
    %14 = "llvm.mlir.constant"() <{ "value" = 32 : i32 }> : () -> i32
    "func.return"(%7, %12, %13) : (!llvm.byte<64>, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b000000000000000000000000????????00000000000000000000000000010001#64, poison, 0x00000011#32]
