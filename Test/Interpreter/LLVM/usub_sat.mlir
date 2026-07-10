// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %c10 = "llvm.mlir.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %c30 = "llvm.mlir.constant"() <{ "value" = 30 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 10 - 30 borrows -> saturate to 0 (0x00)
    %lo = "llvm.intr.usub.sat"(%c10, %c30) : (i8, i8) -> i8
    // 30 - 10 = 20, no borrow (0x14)
    %ok = "llvm.intr.usub.sat"(%c30, %c10) : (i8, i8) -> i8
    // poison operand -> poison
    %p = "llvm.intr.usub.sat"(%c30, %poison) : (i8, i8) -> i8
    "func.return"(%lo, %ok, %p) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, 0x14#8, poison]
