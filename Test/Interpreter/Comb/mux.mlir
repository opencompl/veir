// RUN: veir-interpret %s | filecheck %s

// `comb.mux` is tested through the MLIR parser. Tests for asymmetry between the inputs: poison
// in the unchosen arm cannot reach the result, which is what lets a mux guard an undefined
// computation, while poison in the condition selects nothing and so stays poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8)}> ({
    %t = "hw.constant"() <{ "value" = 1 : i1 }> : () -> i1
    %f = "hw.constant"() <{ "value" = 0 : i1 }> : () -> i1
    %caa = "hw.constant"() <{ "value" = 170 : i8 }> : () -> i8
    %c55 = "hw.constant"() <{ "value" = 85 : i8 }> : () -> i8
    %c5 = "hw.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %cff = "hw.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %c1 = "hw.constant"() <{ "value" = 1 : i1 }> : () -> i1

    // Both arms defined: an ordinary selection, pinned in both directions so the test cannot
    // pass on a mux that always returns one side.
    %sel_t = "comb.mux"(%t, %caa, %c55) : (i1, i8, i8) -> i8
    %sel_f = "comb.mux"(%f, %caa, %c55) : (i1, i8, i8) -> i8

    %undef = "llvm.add"(%cff, %c5) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8

    // Poison in the arm that was not chosen does not propagate.
    %guard_t = "comb.mux"(%t, %caa, %undef) : (i1, i8, i8) -> i8
    %guard_f = "comb.mux"(%f, %undef, %c55) : (i1, i8, i8) -> i8

    // Poison in the condition selects nothing, so the result is poison.
    %undef_cond = "llvm.add"(%c1, %c1) <{"overflowFlags" = 3 : i32}> : (i1, i1) -> i1
    %no_sel = "comb.mux"(%undef_cond, %caa, %c55) : (i1, i8, i8) -> i8

    "func.return"(%sel_t, %sel_f, %guard_t, %guard_f, %no_sel) : (i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xaa#8, 0x55#8, 0xaa#8, 0x55#8, poison]
