// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %nine = "llvm.mlir.constant"() <{ "value" = 9 : i8 }> : () -> i8
    // signed max: 7 vs -7 -> 7
    %x = "llvm.intr.smax"(%seven, %negseven) : (i8, i8) -> i8
    // signed max: -7 vs -7 -> -7
    %y = "llvm.intr.smax"(%negseven, %negseven) : (i8, i8) -> i8
    // signed max: 7 vs 9 -> 9
    %z = "llvm.intr.smax"(%seven, %nine) : (i8, i8) -> i8
    "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0xf9#8, 0x09#8]
