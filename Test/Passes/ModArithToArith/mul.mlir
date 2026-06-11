// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s

// Lowering of mod_arith.mul into the arith dialect. The product is computed in a double-width
// intermediate type (i64) so it cannot overflow before the final reduction, then packed to i32.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %r = "mod_arith.mul"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%r) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i64
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i64
// CHECK-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[Q]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[T:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()
