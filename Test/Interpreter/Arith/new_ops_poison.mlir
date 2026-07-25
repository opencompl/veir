// RUN: veir-interpret %s | filecheck %s

// A poison operand propagates to the result of each new op (both results, for
// the multi-result ops). Poison is produced here via an nuw addi overflow.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1, i8, i8, i8, i8)}> ({
    %c255 = "arith.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %c3   = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c5   = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %poison = "arith.addi"(%c255, %c3) <{"overflowFlags" = #arith.overflow<nuw>}> : (i8, i8) -> i8
    %maxs = "arith.maxsi"(%poison, %c5) : (i8, i8) -> i8
    %cmp  = "arith.cmpi"(%poison, %c5) <{ "predicate" = 2 : i64 }> : (i8, i8) -> i1
    %asum, %aov = "arith.addui_extended"(%poison, %c5) : (i8, i8) -> (i8, i1)
    %mlo, %mhi = "arith.mulsi_extended"(%poison, %c3) : (i8, i8) -> (i8, i8)
    %cs = "arith.ceildivsi"(%poison, %c5) : (i8, i8) -> i8
    %fs = "arith.floordivsi"(%poison, %c5) : (i8, i8) -> i8
    "func.return"(%maxs, %cmp, %asum, %aov, %mlo, %mhi, %cs, %fs) : (i8, i1, i8, i1, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, poison, poison, poison, poison, poison, poison]
