// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s --check-prefix=REMUI
// RUN: veir-opt %s -p='mod-arith-to-arith{barrett}' | filecheck %s --check-prefix=BARRETT
// RUN: veir-opt %s -p='mod-arith-to-arith{pow2-width}' | filecheck %s --check-prefix=REMUI_POW2
// RUN: veir-opt %s -p='mod-arith-to-arith{barrett pow2-width}' | filecheck %s --check-prefix=BARRETT_POW2

// Lowering of mod_arith.mul into the arith dialect. The non-power-of-two i33 storage width
// distinguishes the exact-width and power-of-two-width options.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i33>, !mod_arith.int<7 : i33>) -> !mod_arith.int<7 : i33>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i33>, %1 : !mod_arith.int<7 : i33>):
      %r = "mod_arith.mul"(%0, %1) : (!mod_arith.int<7 : i33>, !mod_arith.int<7 : i33>) -> !mod_arith.int<7 : i33>
      "func.return"(%r) : (!mod_arith.int<7 : i33>) -> ()
  }) : () -> ()
}) : () -> ()

// REMUI:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i33>, [[ARG1:%.*]] : !mod_arith.int<7 : i33>):
// REMUI-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i33>) -> i33
// REMUI-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i33) -> i66
// REMUI-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i33>) -> i33
// REMUI-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i33) -> i66
// REMUI-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i66, i66) -> i66
// REMUI-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i66}> : () -> i66
// REMUI-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[Q]]) : (i66, i66) -> i66
// REMUI-NEXT:   [[T:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66) -> i33
// REMUI-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i33) -> !mod_arith.int<7 : i33>
// REMUI-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i33>) -> ()

// BARRETT:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i33>, [[ARG1:%.*]] : !mod_arith.int<7 : i33>):
// BARRETT-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i33>) -> i33
// BARRETT-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i33) -> i66
// BARRETT-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i33>) -> i33
// BARRETT-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i33) -> i66
// BARRETT-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i66, i66) -> i66
// BARRETT-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i66}> : () -> i66
// BARRETT-NEXT:   [[MU:%.*]] = "arith.constant"() <{"value" = 9 : i66}> : () -> i66
// BARRETT-NEXT:   [[SHIFT:%.*]] = "arith.constant"() <{"value" = 6 : i66}> : () -> i66
// BARRETT-NEXT:   [[PRODUCT:%.*]] = "arith.muli"([[PROD]], [[MU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66, i66) -> i66
// BARRETT-NEXT:   [[REDUCED:%.*]] = "arith.shrui"([[PRODUCT]], [[SHIFT]]) : (i66, i66) -> i66
// BARRETT-NEXT:   [[REDUCED_Q:%.*]] = "arith.muli"([[REDUCED]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66, i66) -> i66
// BARRETT-NEXT:   [[REM:%.*]] = "arith.subi"([[PROD]], [[REDUCED_Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66, i66) -> i66
// BARRETT-NEXT:   [[GE:%.*]] = "arith.cmpi"([[REM]], [[Q]]) <{"predicate" = 9 : i64}> : (i66, i66) -> i1
// BARRETT-NEXT:   [[REM_Q:%.*]] = "arith.subi"([[REM]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66, i66) -> i66
// BARRETT-NEXT:   [[SELECT:%.*]] = "arith.select"([[GE]], [[REM_Q]], [[REM]]) : (i1, i66, i66) -> i66
// BARRETT-NEXT:   [[T:%.*]] = "arith.trunci"([[SELECT]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i66) -> i33
// BARRETT-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i33) -> !mod_arith.int<7 : i33>
// BARRETT-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i33>) -> ()

// REMUI_POW2:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i33>, [[ARG1:%.*]] : !mod_arith.int<7 : i33>):
// REMUI_POW2-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i33>) -> i64
// REMUI_POW2-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i64) -> i128
// REMUI_POW2-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i33>) -> i64
// REMUI_POW2-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i64) -> i128
// REMUI_POW2-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i128, i128) -> i128
// REMUI_POW2-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i128}> : () -> i128
// REMUI_POW2-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[Q]]) : (i128, i128) -> i128
// REMUI_POW2-NEXT:   [[T:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128) -> i64
// REMUI_POW2-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i64) -> !mod_arith.int<7 : i33>
// REMUI_POW2-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i33>) -> ()

// BARRETT_POW2:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i33>, [[ARG1:%.*]] : !mod_arith.int<7 : i33>):
// BARRETT_POW2-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i33>) -> i64
// BARRETT_POW2-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i64) -> i128
// BARRETT_POW2-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i33>) -> i64
// BARRETT_POW2-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i64) -> i128
// BARRETT_POW2-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i128}> : () -> i128
// BARRETT_POW2-NEXT:   [[MU:%.*]] = "arith.constant"() <{"value" = 9 : i128}> : () -> i128
// BARRETT_POW2-NEXT:   [[SHIFT:%.*]] = "arith.constant"() <{"value" = 6 : i128}> : () -> i128
// BARRETT_POW2-NEXT:   [[PRODUCT:%.*]] = "arith.muli"([[PROD]], [[MU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[REDUCED:%.*]] = "arith.shrui"([[PRODUCT]], [[SHIFT]]) : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[REDUCED_Q:%.*]] = "arith.muli"([[REDUCED]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[REM:%.*]] = "arith.subi"([[PROD]], [[REDUCED_Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[GE:%.*]] = "arith.cmpi"([[REM]], [[Q]]) <{"predicate" = 9 : i64}> : (i128, i128) -> i1
// BARRETT_POW2-NEXT:   [[REM_Q:%.*]] = "arith.subi"([[REM]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[SELECT:%.*]] = "arith.select"([[GE]], [[REM_Q]], [[REM]]) : (i1, i128, i128) -> i128
// BARRETT_POW2-NEXT:   [[T:%.*]] = "arith.trunci"([[SELECT]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128) -> i64
// BARRETT_POW2-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i64) -> !mod_arith.int<7 : i33>
// BARRETT_POW2-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i33>) -> ()
