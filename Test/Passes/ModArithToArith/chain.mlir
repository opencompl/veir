// RUN: veir-opt %s -p="mod-arith-to-arith,reconcile-cast" | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %a = "mod_arith.add"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      %b = "mod_arith.mul"(%a, %a) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%b) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// input casts are kept
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i33
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i33

// "middle" casts are reconciled away
// CHECK-NEXT:   [[QADD:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// CHECK-NEXT:   [[SUM:%.*]] = "arith.addi"([[E0]], [[E1]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[SUMR:%.*]] = "arith.remui"([[SUM]], [[QADD]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[ADD:%.*]] = "arith.trunci"([[SUMR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
// CHECK-NEXT:   [[M0:%.*]] = "arith.extui"([[ADD]]) : (i32) -> i64
// CHECK-NEXT:   [[M1:%.*]] = "arith.extui"([[ADD]]) : (i32) -> i64
// CHECK-NEXT:   [[QMUL:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:   [[PROD:%.*]] = "arith.muli"([[M0]], [[M1]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[QMUL]]) : (i64, i64) -> i64

// output casts are kept
// CHECK-NEXT:   [[MUL:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[MUL]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()
