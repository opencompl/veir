// RUN: veir-interpret %s | filecheck %s

// Subtraction and the three shifts are tested through the MLIR parser. The boundary conditions
// for the shifts are checked at the operand width and one bit beyond, where `comb` yields poison
// and `BitVec.shiftLeft` would yield zero.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %c0 = "hw.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %c1 = "hw.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %c2 = "hw.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %c3 = "hw.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c5 = "hw.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %c8 = "hw.constant"() <{ "value" = 8 : i8 }> : () -> i8
    %c9 = "hw.constant"() <{ "value" = 9 : i8 }> : () -> i8
    // 0b10010000, negative when read as signed.
    %c90 = "hw.constant"() <{ "value" = 144 : i8 }> : () -> i8

    // Wraps rather than saturating: 3 - 5 is 254.
    %sub = "comb.sub"(%c3, %c5) : (i8, i8) -> i8

    %shl = "comb.shl"(%c3, %c2) : (i8, i8) -> i8
    // Bits shifted past the top are dropped.
    %shl_top = "comb.shl"(%c90, %c1) : (i8, i8) -> i8
    %shl_zero = "comb.shl"(%c3, %c0) : (i8, i8) -> i8

    // The logical and arithmetic shifts are required to differ on a negative operand.
    %shru = "comb.shru"(%c90, %c1) : (i8, i8) -> i8
    %shrs = "comb.shrs"(%c90, %c1) : (i8, i8) -> i8

    // At the width and beyond it: poison, where a hardware shifter would do something else.
    %shl_at = "comb.shl"(%c3, %c8) : (i8, i8) -> i8
    %shru_past = "comb.shru"(%c3, %c9) : (i8, i8) -> i8

    "func.return"(%sub, %shl, %shl_top, %shl_zero, %shru, %shrs, %shl_at, %shru_past) : (i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfe#8, 0x0c#8, 0x20#8, 0x03#8, 0x48#8, 0xc8#8, poison, poison]
