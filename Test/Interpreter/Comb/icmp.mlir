// RUN: veir-interpret %s | filecheck %s

// `comb.icmp` is tested through the MLIR parser, where the predicate arrives as an integer
// attribute rather than as a Lean constructor. The signed and unsigned pairs are checked on the
// same bits and required to disagree, so a table with `slt` and `ult` transposed cannot pass.
// Each ordering predicate is then checked again with its operands swapped, which is what
// separates a predicate from its converse: a table with `slt` and `sgt` transposed answers every
// unswapped case correctly and every swapped one backwards.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1)}> ({
    // 240 unsigned, -16 signed.
    %a = "hw.constant"() <{ "value" = 240 : i8 }> : () -> i8
    %b = "hw.constant"() <{ "value" = 16 : i8 }> : () -> i8

    %eq = "comb.icmp"(%a, %b) <{"predicate" = 0 : i64}> : (i8, i8) -> i1
    %ne = "comb.icmp"(%a, %b) <{"predicate" = 1 : i64}> : (i8, i8) -> i1

    // -16 < 16 holds; 240 < 16 does not.
    %slt = "comb.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i8, i8) -> i1
    %ult = "comb.icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i8, i8) -> i1

    // The same disagreement the other way round.
    %sgt = "comb.icmp"(%a, %b) <{"predicate" = 4 : i64}> : (i8, i8) -> i1
    %ugt = "comb.icmp"(%a, %b) <{"predicate" = 8 : i64}> : (i8, i8) -> i1

    %sle = "comb.icmp"(%a, %b) <{"predicate" = 3 : i64}> : (i8, i8) -> i1
    %uge = "comb.icmp"(%a, %b) <{"predicate" = 9 : i64}> : (i8, i8) -> i1

    // Equality on equal operands, so the table is not passing by always answering false.
    %eq_self = "comb.icmp"(%b, %b) <{"predicate" = 0 : i64}> : (i8, i8) -> i1

    // The same four orderings with the operands swapped. Every answer is the converse of the
    // one above, so a predicate exchanged with its converse is caught here and nowhere else.
    %slt_swapped = "comb.icmp"(%b, %a) <{"predicate" = 2 : i64}> : (i8, i8) -> i1
    %ult_swapped = "comb.icmp"(%b, %a) <{"predicate" = 6 : i64}> : (i8, i8) -> i1
    %sgt_swapped = "comb.icmp"(%b, %a) <{"predicate" = 4 : i64}> : (i8, i8) -> i1
    %ugt_swapped = "comb.icmp"(%b, %a) <{"predicate" = 8 : i64}> : (i8, i8) -> i1

    "func.return"(%eq, %ne, %slt, %ult, %sgt, %ugt, %sle, %uge, %eq_self, %slt_swapped, %ult_swapped, %sgt_swapped, %ugt_swapped) : (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0#1, 0x1#1, 0x1#1, 0x0#1, 0x0#1, 0x1#1, 0x1#1, 0x1#1, 0x1#1, 0x0#1, 0x1#1, 0x1#1, 0x0#1]
