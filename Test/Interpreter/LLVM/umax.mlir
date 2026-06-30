// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %seven = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %negseven = "llvm.mlir.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %nine = "llvm.mlir.constant"() <{ "value" = 9 : i8 }> : () -> i8
    // unsigned max: 7 vs -7 (=249) -> 249 (0xf9)
    %x = "llvm.intr.umax"(%seven, %negseven) : (i8, i8) -> i8
    // unsigned max: 7 vs 9 -> 9
    %y = "llvm.intr.umax"(%seven, %nine) : (i8, i8) -> i8
    // unsigned max: 7 vs 7 -> 7
    %z = "llvm.intr.umax"(%seven, %seven) : (i8, i8) -> i8
    "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xf9#8, 0x09#8, 0x07#8]
