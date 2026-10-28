// RUN: veir-interpret %s | filecheck %s

// The variadic integer operations are tested through the MLIR parser; `add.mlir` already covers
// `add`. Each operation folds its operands from a unit -- the identity element for that
// operation, which is 1 for `mul` and all ones for `and` -- and each unit is checked by a
// single-operand fold, which returns the unit combined with the one operand and so is the case
// where a wrong unit shows up on its own.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    %c2 = "hw.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %c3 = "hw.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c5 = "hw.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %c7 = "hw.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %caa = "hw.constant"() <{ "value" = 170 : i8 }> : () -> i8
    %ccc = "hw.constant"() <{ "value" = 204 : i8 }> : () -> i8
    %cff = "hw.constant"() <{ "value" = 255 : i8 }> : () -> i8

    %mul2 = "comb.mul"(%c3, %c5) : (i8, i8) -> i8
    %mul3 = "comb.mul"(%c3, %c5, %c2) : (i8, i8, i8) -> i8
    // One operand: the fold returns the operand only if the unit is one.
    %mul1 = "comb.mul"(%c7) : (i8) -> i8

    %and2 = "comb.and"(%ccc, %caa) : (i8, i8) -> i8
    // One operand again: the unit here is all ones, not zero.
    %and1 = "comb.and"(%c7) : (i8) -> i8

    %or2 = "comb.or"(%ccc, %caa) : (i8, i8) -> i8
    %xor2 = "comb.xor"(%ccc, %caa) : (i8, i8) -> i8
    // CIRCT's idiom for `not`, which is why `comb` declines to carry one.
    %xornot = "comb.xor"(%caa, %cff) : (i8, i8) -> i8

    // Poison from an `nuw` overflow, propagating through a variadic fold.
    %nuw_nsw = "llvm.add"(%cff, %c5) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8
    %poison = "comb.mul"(%nuw_nsw, %c5) : (i8, i8) -> i8

    "func.return"(%mul2, %mul3, %mul1, %and2, %and1, %or2, %xor2, %xornot, %poison) : (i8, i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0f#8, 0x1e#8, 0x07#8, 0x88#8, 0x07#8, 0xee#8, 0x66#8, 0x55#8, poison]
