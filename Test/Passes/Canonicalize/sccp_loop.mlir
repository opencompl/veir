// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A constant carried through an unknown backedge remains constant, allowing
// SCCP to mark the true edge of the comparison unreachable.
"builtin.module"() ({
  "func.func"() <{sym_name = "sccp_loop", function_type = () -> i32}> ({
^bb0:
  %x0 = "arith.constant"() <{value = 1 : i32}> : () -> i32
  "cf.br"(%x0) [^bb1] : (i32) -> ()
^bb1(%x1 : i32):
  // CHECK-LABEL: func.func @sccp_loop
  // CHECK-NEXT: %[[ONE:.*]] = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
  // CHECK-NEXT: %[[FALSE:.*]] = "arith.constant"() <{"value" = false}> : () -> i1
  // CHECK:      ^{{[0-9]+}}(%{{.*}} : i32):
  // CHECK-NEXT: "cf.cond_br"(%[[FALSE]], %[[ONE]], %[[ONE]])
  // CHECK:      %[[PRED:.*]] = "test.test"() : () -> i1
  // CHECK-NEXT: "cf.cond_br"(%[[PRED]], %{{.*}}, %{{.*}})
  // CHECK-NEXT: ^{{[0-9]+}}(%{{.*}} : i32):
  // CHECK-NEXT: "func.return"(%[[ONE]]) : (i32) -> ()
  %one = "arith.constant"() <{value = 1 : i32}> : () -> i32
  %b = "arith.cmpi"(%x1, %one) <{predicate = 1 : i64}> : (i32, i32) -> i1
  "cf.cond_br"(%b, %x1, %x1) [^bb2, ^bb3]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^bb2(%x1_then : i32):
  %x2 = "arith.constant"() <{value = 2 : i32}> : () -> i32
  "cf.br"(%x2) [^bb3] : (i32) -> ()
^bb3(%x3 : i32):
  %pred = "test.test"() : () -> i1
  "cf.cond_br"(%pred, %x3, %x3) [^bb1, ^bb4]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^bb4(%retv : i32):
  "func.return"(%retv) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
