// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s --check-prefix=REMUI
// RUN: veir-opt %s -p='mod-arith-to-arith{barrett}' | filecheck %s --check-prefix=BARRETT
// RUN: veir-opt %s -p='mod-arith-to-arith{pow2-width}' | filecheck %s --check-prefix=REMUI_POW2
// RUN: veir-opt %s -p='mod-arith-to-arith{barrett pow2-width}' | filecheck %s --check-prefix=BARRETT_POW2

// Lowering of mod_arith.sub into the arith dialect. To avoid unsigned underflow when lhs < rhs,
// the difference is computed as (a + q) - b in a wider intermediate type (i33 exactly, or i64
// with power-of-two widths), which stays in (0, 2q), before reduction and packing.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %r = "mod_arith.sub"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%r) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// REMUI:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// REMUI-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// REMUI-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i33
// REMUI-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// REMUI-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i33
// REMUI-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// REMUI-NEXT:   [[AQ:%.*]] = "arith.addi"([[E0]], [[Q]]) : (i33, i33) -> i33
// REMUI-NEXT:   [[DIFF:%.*]] = "arith.subi"([[AQ]], [[E1]]) : (i33, i33) -> i33
// REMUI-NEXT:   [[QR:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// REMUI-NEXT:   [[DIFFR:%.*]] = "arith.remui"([[DIFF]], [[QR]]) : (i33, i33) -> i33
// REMUI-NEXT:   [[T:%.*]] = "arith.trunci"([[DIFFR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
// REMUI-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// REMUI-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()

// BARRETT:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// BARRETT-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// BARRETT-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i33
// BARRETT-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// BARRETT-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i33
// BARRETT-NEXT:   [[QADD:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// BARRETT-NEXT:   [[AQ:%.*]] = "arith.addi"([[E0]], [[QADD]]) : (i33, i33) -> i33
// BARRETT-NEXT:   [[DIFF:%.*]] = "arith.subi"([[AQ]], [[E1]]) : (i33, i33) -> i33
// BARRETT-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// BARRETT-NEXT:   [[MU:%.*]] = "arith.constant"() <{"value" = 9 : i33}> : () -> i33
// BARRETT-NEXT:   [[SHIFT:%.*]] = "arith.constant"() <{"value" = 6 : i33}> : () -> i33
// BARRETT-NEXT:   [[PRODUCT:%.*]] = "arith.muli"([[DIFF]], [[MU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33, i33) -> i33
// BARRETT-NEXT:   [[REDUCED:%.*]] = "arith.shrui"([[PRODUCT]], [[SHIFT]]) : (i33, i33) -> i33
// BARRETT-NEXT:   [[REDUCED_Q:%.*]] = "arith.muli"([[REDUCED]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33, i33) -> i33
// BARRETT-NEXT:   [[REM:%.*]] = "arith.subi"([[DIFF]], [[REDUCED_Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33, i33) -> i33
// BARRETT-NEXT:   [[GE:%.*]] = "arith.cmpi"([[REM]], [[Q]]) <{"predicate" = 9 : i64}> : (i33, i33) -> i1
// BARRETT-NEXT:   [[REM_Q:%.*]] = "arith.subi"([[REM]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33, i33) -> i33
// BARRETT-NEXT:   [[SELECT:%.*]] = "arith.select"([[GE]], [[REM_Q]], [[REM]]) : (i1, i33, i33) -> i33
// BARRETT-NEXT:   [[T:%.*]] = "arith.trunci"([[SELECT]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
// BARRETT-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// BARRETT-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()

// REMUI_POW2:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// REMUI_POW2-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// REMUI_POW2-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i64
// REMUI_POW2-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// REMUI_POW2-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i64
// REMUI_POW2-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// REMUI_POW2-NEXT:   [[AQ:%.*]] = "arith.addi"([[E0]], [[Q]]) : (i64, i64) -> i64
// REMUI_POW2-NEXT:   [[DIFF:%.*]] = "arith.subi"([[AQ]], [[E1]]) : (i64, i64) -> i64
// REMUI_POW2-NEXT:   [[QR:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// REMUI_POW2-NEXT:   [[DIFFR:%.*]] = "arith.remui"([[DIFF]], [[QR]]) : (i64, i64) -> i64
// REMUI_POW2-NEXT:   [[T:%.*]] = "arith.trunci"([[DIFFR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// REMUI_POW2-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// REMUI_POW2-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()

// BARRETT_POW2:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// BARRETT_POW2-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// BARRETT_POW2-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i64
// BARRETT_POW2-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// BARRETT_POW2-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i64
// BARRETT_POW2-NEXT:   [[QADD:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// BARRETT_POW2-NEXT:   [[AQ:%.*]] = "arith.addi"([[E0]], [[QADD]]) : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[DIFF:%.*]] = "arith.subi"([[AQ]], [[E1]]) : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// BARRETT_POW2-NEXT:   [[MU:%.*]] = "arith.constant"() <{"value" = 9 : i64}> : () -> i64
// BARRETT_POW2-NEXT:   [[SHIFT:%.*]] = "arith.constant"() <{"value" = 6 : i64}> : () -> i64
// BARRETT_POW2-NEXT:   [[PRODUCT:%.*]] = "arith.muli"([[DIFF]], [[MU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[REDUCED:%.*]] = "arith.shrui"([[PRODUCT]], [[SHIFT]]) : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[REDUCED_Q:%.*]] = "arith.muli"([[REDUCED]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[REM:%.*]] = "arith.subi"([[DIFF]], [[REDUCED_Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[GE:%.*]] = "arith.cmpi"([[REM]], [[Q]]) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
// BARRETT_POW2-NEXT:   [[REM_Q:%.*]] = "arith.subi"([[REM]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[SELECT:%.*]] = "arith.select"([[GE]], [[REM_Q]], [[REM]]) : (i1, i64, i64) -> i64
// BARRETT_POW2-NEXT:   [[T:%.*]] = "arith.trunci"([[SELECT]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// BARRETT_POW2-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// BARRETT_POW2-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()
