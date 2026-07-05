// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8)}> ({
    %c200 = "llvm.mlir.constant"() <{ "value" = 200 : i8 }> : () -> i8
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c10 = "llvm.mlir.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 200 + 100 = 300 overflows above UINT8_MAX -> saturate to 255 (0xff)
    %hi = "llvm.intr.uadd.sat"(%c200, %c100) : (i8, i8) -> i8
    // 200 + 10 = 210, no overflow (0xd2)
    %ok = "llvm.intr.uadd.sat"(%c200, %c10) : (i8, i8) -> i8
    // poison operand -> poison
    %p = "llvm.intr.uadd.sat"(%c200, %poison) : (i8, i8) -> i8
    "func.return"(%hi, %ok, %p) : (i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0xd2#8, poison]
