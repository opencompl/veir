// RUN: veir-opt %s -p=mod-arith-to-arith | filecheck %s

// Lowering of mod_arith.sub into the arith dialect. To avoid unsigned underflow when lhs < rhs,
// the difference is computed as (a + q) - b in a wider intermediate type (i33), which stays in
// (0, 2q), before reducing modulo q and packing back down.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %r = "mod_arith.sub"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%r) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i33
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i33
// CHECK-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// CHECK-NEXT:   [[AQ:%.*]] = "arith.addi"([[E0]], [[Q]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[DIFF:%.*]] = "arith.subi"([[AQ]], [[E1]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[DIFFR:%.*]] = "arith.remui"([[DIFF]], [[Q]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[T:%.*]] = "arith.trunci"([[DIFFR]]) <{"overflowFlags" = 2 : i32}> : (i33) -> i32
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[T]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()
