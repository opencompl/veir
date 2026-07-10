// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %cn100 = "llvm.mlir.constant"() <{ "value" = -100 : i8 }> : () -> i8
    %cn50 = "llvm.mlir.constant"() <{ "value" = -50 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 100 + 50 = 150 overflows above INT8_MAX -> saturate to 127 (0x7f)
    %hi = "llvm.intr.sadd.sat"(%c100, %c50) : (i8, i8) -> i8
    // -100 + -50 = -150 overflows below INT8_MIN -> saturate to -128 (0x80)
    %lo = "llvm.intr.sadd.sat"(%cn100, %cn50) : (i8, i8) -> i8
    // 100 + -50 = 50, no overflow (0x32)
    %ok = "llvm.intr.sadd.sat"(%c100, %cn50) : (i8, i8) -> i8
    // poison operand -> poison
    %p = "llvm.intr.sadd.sat"(%c100, %poison) : (i8, i8) -> i8
    "func.return"(%hi, %lo, %ok, %p) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x7f#8, 0x80#8, 0x32#8, poison]
