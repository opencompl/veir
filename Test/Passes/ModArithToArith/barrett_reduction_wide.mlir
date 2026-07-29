// RUN: veir-opt %s -p=remui-to-barrett-reduction | filecheck %s

// q = 12289 (k = 14) on i32: r * mu needs 3k = 42 bits,
// so the reduction is computed at i42 and wrapped in extui/trunci 

"builtin.module"() ({
  "func.func"() <{"function_type" = (i32, i32) -> i32, "sym_name" = "barrett_widened"}> ({
  ^bb0(%arg0: i32, %arg1: i32):
    %0 = "arith.constant"() <{"value" = 12289 : i32}> : () -> i32
    %1 = "arith.muli"(%arg0, %arg1) : (i32, i32) -> i32
    %2 = "arith.remui"(%1, %0) : (i32, i32) -> i32
    "func.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[A0:%.*]] : i32, [[A1:%.*]] : i32):
// CHECK-NEXT:     [[R:%.*]] = "arith.muli"([[A0]], [[A1]]) : (i32, i32) -> i32
// CHECK-NEXT:     [[RW:%.*]] = "arith.extui"([[R]]) : (i32) -> i42
// CHECK-NEXT:     [[Q:%.*]] = "arith.constant"() <{"value" = 12289 : i42}> : () -> i42
// CHECK-NEXT:     [[MU:%.*]] = "arith.constant"() <{"value" = 21843 : i42}> : () -> i42
// CHECK-NEXT:     [[SH:%.*]] = "arith.constant"() <{"value" = 28 : i42}> : () -> i42
// CHECK-NEXT:     [[P:%.*]] = "arith.muli"([[RW]], [[MU]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[E:%.*]] = "arith.shrui"([[P]], [[SH]]) : (i42, i42) -> i42
// CHECK-NEXT:     [[EQ:%.*]] = "arith.muli"([[E]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[REM:%.*]] = "arith.subi"([[RW]], [[EQ]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[GE:%.*]] = "arith.cmpi"([[REM]], [[Q]]) <{"predicate" = 9 : i64}> : (i42, i42) -> i1
// CHECK-NEXT:     [[REMQ:%.*]] = "arith.subi"([[REM]], [[Q]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42, i42) -> i42
// CHECK-NEXT:     [[RES:%.*]] = "arith.select"([[GE]], [[REMQ]], [[REM]]) : (i1, i42, i42) -> i42
// CHECK-NEXT:     [[OUT:%.*]] = "arith.trunci"([[RES]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i42) -> i32
// CHECK-NEXT:     "func.return"([[OUT]]) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
