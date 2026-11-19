// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i13, i13)}> ({
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %cn100 = "llvm.mlir.constant"() <{ "value" = -100 : i8 }> : () -> i8
    %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 100 * 50 = 5000 = 0x1388; the high half is 0x13.
    %pos = "gmir.g_umulh"(%c100, %c50) : (i8, i8) -> i8
    // The bits of -100 read unsigned are 156; 156 * 50 = 7800 = 0x1e78, so the
    // high half is 0x1e, where `gmir.g_smulh` gives 0xec.
    %other = "gmir.g_umulh"(%cn100, %c50) : (i8, i8) -> i8
    // 3 * 50 = 150 fits in 8 bits, so the high half is zero.
    %small = "gmir.g_umulh"(%c3, %c50) : (i8, i8) -> i8
    // A poison operand gives poison.
    %p = "gmir.g_umulh"(%c100, %poison) : (i8, i8) -> i8
    %c4000 = "llvm.mlir.constant"() <{ "value" = 4000 : i13 }> : () -> i13
    %cn4000 = "llvm.mlir.constant"() <{ "value" = -4000 : i13 }> : () -> i13
    %c4095 = "llvm.mlir.constant"() <{ "value" = 4095 : i13 }> : () -> i13
    %c3w = "llvm.mlir.constant"() <{ "value" = 3 : i13 }> : () -> i13
    // An odd width: the bits of -4000 read unsigned are 4192, and 4192 * 3 =
    // 12576 has high 13 bits 1, where `g_smulh` gives -2.
    %w1 = "gmir.g_umulh"(%cn4000, %c3w) : (i13, i13) -> i13
    // 4095 * 4095 = 16769025, whose high 13 bits are 2047.
    %w2 = "gmir.g_umulh"(%c4095, %c4095) : (i13, i13) -> i13
    "func.return"(%pos, %other, %small, %p, %w1, %w2) : (i8, i8, i8, i8, i13, i13) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x13#8, 0x1e#8, 0x00#8, poison, 0x0001#13, 0x07ff#13]
