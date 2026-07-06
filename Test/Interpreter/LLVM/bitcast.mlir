// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<64>, i64, i64)}> ({
    %3 = "llvm.mlir.poison"() : () -> i64
    %4 = "llvm.mlir.constant"() <{ "value" = 32 : i64 }> : () -> i64
    %5 = "llvm.bitcast"(%3) : (i64) -> !llvm.byte<64>
    %6 = "llvm.lshr"(%5, %4) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %7 = "llvm.lshr"(%6, %4) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %8 = "llvm.bitcast"(%6) : (!llvm.byte<64>) -> i64
    %9 = "llvm.bitcast"(%7) : (!llvm.byte<64>) -> i64
    "func.return"(%6, %8, %9) : (!llvm.byte<64>, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b00000000000000000000000000000000????????????????????????????????#64, poison, 0x0000000000000000#64]
