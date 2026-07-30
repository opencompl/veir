// RUN: veir-opt %s -p=mod-arith-to-arith-pow2-width | filecheck %s

// Width-normalized lowering of mod_arith.mul with a non-power-of-two storage type (i33).
// The representation type crossing op boundaries is the normalized storage width (i64),
// so no i33 arith value survives; the double-width intermediate (i66 -> i128) exists only
// between the extui and trunci of this op's own cluster.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i33>, !mod_arith.int<7 : i33>) -> !mod_arith.int<7 : i33>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i33>, %1 : !mod_arith.int<7 : i33>):
      %r = "mod_arith.mul"(%0, %1) : (!mod_arith.int<7 : i33>, !mod_arith.int<7 : i33>) -> !mod_arith.int<7 : i33>
      "func.return"(%r) : (!mod_arith.int<7 : i33>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i33>, [[ARG1:%.*]] : !mod_arith.int<7 : i33>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i33>) -> i64
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i64) -> i128
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i33>) -> i64
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i64) -> i128
// CHECK-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i128}> : () -> i128
// CHECK-NEXT:   [[PROD:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[Q]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[T:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128) -> i64
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i64) -> !mod_arith.int<7 : i33>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i33>) -> ()
