// RUN: veir-interpret %s | filecheck %s

// `comb.concat` and `comb.extract` are tested through the MLIR parser, where `lowBit` arrives as
// an attribute and the result width as a type. Both operand orders of `concat` are checked,
// since swapping the two operands still type-checks and still verifies; `extract` is checked at
// two result widths from the same operand, since taking the width from the operand instead of
// the type would be undetectable at a single width.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i2, i4, i4)}> ({
    %ca = "hw.constant"() <{ "value" = 10 : i4 }> : () -> i4
    %cb = "hw.constant"() <{ "value" = 11 : i4 }> : () -> i4
    // 0b1010_0111. The low two bits are 3 and the low four are 7, so the two extractions
    // below are required to differ -- 0xA3 would give 3 for both.
    %ca7 = "hw.constant"() <{ "value" = 167 : i8 }> : () -> i8

    // Most significant operand first, as `BitVec.++` has it.
    %concat_ab = "comb.concat"(%ca, %cb) : (i4, i4) -> i8
    %concat_ba = "comb.concat"(%cb, %ca) : (i4, i4) -> i8

    %ext2 = "comb.extract"(%ca7) <{"lowBit" = 0 : i64}> : (i8) -> i2
    %ext4 = "comb.extract"(%ca7) <{"lowBit" = 0 : i64}> : (i8) -> i4
    // A non-zero offset, so the low bits are not the only ones ever read.
    %ext_hi = "comb.extract"(%ca7) <{"lowBit" = 4 : i64}> : (i8) -> i4

    "func.return"(%concat_ab, %concat_ba, %ext2, %ext4, %ext_hi) : (i8, i8, i2, i4, i4) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xab#8, 0xba#8, 0x3#2, 0x7#4, 0xa#4]
