// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i13, i13)}> ({
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %cn100 = "llvm.mlir.constant"() <{ "value" = -100 : i8 }> : () -> i8
    %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // 100 * 50 = 5000 = 0x1388; the high half is 0x13.
    %pos = "gmir.g_smulh"(%c100, %c50) : (i8, i8) -> i8
    // -100 * 50 = -5000 = 0xec78; the high half is 0xec, that is -20.
    %other = "gmir.g_smulh"(%cn100, %c50) : (i8, i8) -> i8
    // 3 * 50 = 150 fits in 8 bits, so the high half is zero.
    %small = "gmir.g_smulh"(%c3, %c50) : (i8, i8) -> i8
    // A poison operand gives poison.
    %p = "gmir.g_smulh"(%c100, %poison) : (i8, i8) -> i8
    %c4000 = "llvm.mlir.constant"() <{ "value" = 4000 : i13 }> : () -> i13
    %cn4000 = "llvm.mlir.constant"() <{ "value" = -4000 : i13 }> : () -> i13
    %c4095 = "llvm.mlir.constant"() <{ "value" = 4095 : i13 }> : () -> i13
    %c3w = "llvm.mlir.constant"() <{ "value" = 3 : i13 }> : () -> i13
    // An odd width: 4000 * 3 = 12000, whose high 13 bits are 1.
    %w1 = "gmir.g_smulh"(%c4000, %c3w) : (i13, i13) -> i13
    // -4000 * 3 = -12000, whose high 13 bits are -2, where `g_umulh` gives 1.
    %w2 = "gmir.g_smulh"(%cn4000, %c3w) : (i13, i13) -> i13
    "func.return"(%pos, %other, %small, %p, %w1, %w2) : (i8, i8, i8, i8, i13, i13) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x13#8, 0xec#8, 0x00#8, poison, 0x0001#13, 0x1ffe#13]
