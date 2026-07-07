// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %c64 = "llvm.mlir.constant"() <{ "value" = 64 : i8 }> : () -> i8
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c2 = "llvm.mlir.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i8 }> : () -> i8
    // 1 << 3 = 8, no overflow (0x08)
    %ok = "llvm.intr.ushl.sat"(%c1, %c3) : (i8, i8) -> i8
    // 64 << 2 = 256 overflows above UINT8_MAX -> saturate to 255 (0xff)
    %hi = "llvm.intr.ushl.sat"(%c64, %c2) : (i8, i8) -> i8
    // 100 << 1 = 200, no overflow (0xc8)
    %ok2 = "llvm.intr.ushl.sat"(%c100, %c1) : (i8, i8) -> i8
    // shift amount == bit width -> poison
    %p = "llvm.intr.ushl.sat"(%c1, %c8) : (i8, i8) -> i8
    "func.return"(%ok, %hi, %ok2, %p) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x08#8, 0xff#8, 0xc8#8, poison]
