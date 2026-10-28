// RUN: veir-interpret %s | filecheck %s

// `comb.parity`, `comb.replicate` and `comb.reverse` are tested through the MLIR parser. Each
// operation is tested on a case an identity function would fail: `reverse` on values that are
// not palindromes as well as on one that is, and `replicate` at two result widths from the same
// operand.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1, i8, i4, i8, i8, i8)}> ({
    // 0b1010_0111, five bits set, so odd parity.
    %ca7 = "hw.constant"() <{ "value" = 167 : i8 }> : () -> i8
    // 0b1010_1010, four bits set, so even parity.
    %caa = "hw.constant"() <{ "value" = 170 : i8 }> : () -> i8
    // 0b1000_0001, a palindrome under bit reversal.
    %c81 = "hw.constant"() <{ "value" = 129 : i8 }> : () -> i8
    // 0b10, replicated below.
    %c2 = "hw.constant"() <{ "value" = 2 : i2 }> : () -> i2

    %parity_odd = "comb.parity"(%ca7) : (i8) -> i1
    %parity_even = "comb.parity"(%caa) : (i8) -> i1

    // The copy count comes from the result width, so the same operand gives different answers.
    %rep8 = "comb.replicate"(%c2) : (i2) -> i8
    %rep4 = "comb.replicate"(%c2) : (i2) -> i4

    %rev = "comb.reverse"(%ca7) : (i8) -> i8
    // A palindrome alone would pass on an identity, so it is paired with values that would not.
    %rev_pal = "comb.reverse"(%c81) : (i8) -> i8
    %rev_aa = "comb.reverse"(%caa) : (i8) -> i8

    "func.return"(%parity_odd, %parity_even, %rep8, %rep4, %rev, %rev_pal, %rev_aa) : (i1, i1, i8, i4, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1#1, 0x0#1, 0xaa#8, 0xa#4, 0xe5#8, 0x81#8, 0x55#8]
