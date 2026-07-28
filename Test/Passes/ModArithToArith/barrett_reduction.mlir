// RUN: veir-opt %s -p=remui-to-barrett-reduction | filecheck %s

// Rewrite of arith.remui into Barrett reduction algorithm using arith dialect. 

"builtin.module"() ({
  "func.func"() <{"function_type" = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, "sym_name" = "main"}> ({
  ^bb0(%arg0: !mod_arith.int<7 : i32>, %arg1: !mod_arith.int<7 : i32>):
    %0 = "builtin.unrealized_conversion_cast"(%arg0) : (!mod_arith.int<7 : i32>) -> i32
    %1 = "arith.extui"(%0) : (i32) -> i64
    %2 = "builtin.unrealized_conversion_cast"(%arg1) : (!mod_arith.int<7 : i32>) -> i32
    %3 = "arith.extui"(%2) : (i32) -> i64
    %4 = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
    %5 = "arith.muli"(%1, %3) : (i64, i64) -> i64
    %6 = "arith.remui"(%5, %4) : (i64, i64) -> i64
    %7 = "arith.trunci"(%6) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
    %8 = "builtin.unrealized_conversion_cast"(%7) : (i32) -> !mod_arith.int<7 : i32>
    "func.return"(%8) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:     [[V0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:     [[V1:%.*]] = "arith.extui"([[V0]]) : (i32) -> i64
// CHECK-NEXT:     [[V2:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:     [[V3:%.*]] = "arith.extui"([[V2]]) : (i32) -> i64
// CHECK-NEXT:     [[C7:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:     [[V4:%.*]] = "arith.muli"([[V1]], [[V3]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[C585:%.*]] = "arith.constant"() <{"value" = 585 : i64}> : () -> i64
// CHECK-NEXT:     [[C12:%.*]] = "arith.constant"() <{"value" = 12 : i64}> : () -> i64
// CHECK-NEXT:     [[V5:%.*]] = "arith.muli"([[V4]], [[C585]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[V6:%.*]] = "arith.shrui"([[V5]], [[C12]]) : (i64, i64) -> i64
// CHECK-NEXT:     [[V7:%.*]] = "arith.muli"([[V6]], [[C7]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[V8:%.*]] = "arith.subi"([[V4]], [[V7]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[V9:%.*]] = "arith.cmpi"([[V8]], [[C7]]) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
// CHECK-NEXT:     [[V10:%.*]] = "arith.subi"([[V8]], [[C7]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64, i64) -> i64
// CHECK-NEXT:     [[V11:%.*]] = "arith.select"([[V9]], [[V10]], [[V8]]) : (i1, i64, i64) -> i64
// CHECK-NEXT:     [[V12:%.*]] = "arith.trunci"([[V11]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// CHECK-NEXT:     [[V13:%.*]] = "builtin.unrealized_conversion_cast"([[V12]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:     "func.return"([[V13]]) : (!mod_arith.int<7 : i32>) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
