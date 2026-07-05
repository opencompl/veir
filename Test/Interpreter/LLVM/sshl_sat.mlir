// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %c32 = "llvm.mlir.constant"() <{ "value" = 32 : i8 }> : () -> i8
    %cn5 = "llvm.mlir.constant"() <{ "value" = -5 : i8 }> : () -> i8
    %c2 = "llvm.mlir.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %c6 = "llvm.mlir.constant"() <{ "value" = 6 : i8 }> : () -> i8
    %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i8 }> : () -> i8
    // 1 << 1 = 2, no overflow (0x02)
    %ok = "llvm.intr.sshl.sat"(%c1, %c1) : (i8, i8) -> i8
    // 32 << 2 = 128 overflows above INT8_MAX -> saturate to 127 (0x7f)
    %hi = "llvm.intr.sshl.sat"(%c32, %c2) : (i8, i8) -> i8
    // -5 << 6 = -320 overflows below INT8_MIN -> saturate to -128 (0x80)
    %lo = "llvm.intr.sshl.sat"(%cn5, %c6) : (i8, i8) -> i8
    // shift amount == bit width -> poison
    %p = "llvm.intr.sshl.sat"(%c1, %c8) : (i8, i8) -> i8
    "func.return"(%ok, %hi, %lo, %p) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x02#8, 0x7f#8, 0x80#8, poison]
