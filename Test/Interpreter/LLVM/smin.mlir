// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %nine = "llvm.mlir.constant"() <{ "value" = 9 : i8 }> : () -> i8
    // signed min: 7 vs -7 -> -7
    %x = "llvm.intr.smin"(%seven, %negseven) : (i8, i8) -> i8
    // signed min: 7 vs 7 -> 7
    %y = "llvm.intr.smin"(%seven, %seven) : (i8, i8) -> i8
    // signed min: 7 vs 9 -> 7
    %z = "llvm.intr.smin"(%seven, %nine) : (i8, i8) -> i8
    "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xf9#8, 0x07#8, 0x07#8]
