// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %nine = "llvm.mlir.constant"() <{ "value" = 9 : i8 }> : () -> i8
    // unsigned min: 7 vs -7 (=249) -> 7
    %x = "llvm.intr.umin"(%seven, %negseven) : (i8, i8) -> i8
    // unsigned min: 7 vs 9 -> 7
    %y = "llvm.intr.umin"(%seven, %nine) : (i8, i8) -> i8
    // unsigned min: -7 (=249) vs -7 -> 249 (0xf9)
    %z = "llvm.intr.umin"(%negseven, %negseven) : (i8, i8) -> i8
    "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0x07#8, 0xf9#8]
