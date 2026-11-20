// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Updating bb5's immediate dominator changes bb3's dominator chain without
// changing bb3's immediate dominator. The analysis must revisit bb2, where
// the path bb0 -> bb1 -> bb5 -> bb3 -> bb2 bypasses the definition in bb4.
"func.func"() <{sym_name = "f", function_type = (i1) -> ()}> ({
^bb0(%cond : i1):
  "cf.cond_br"(%cond) [^bb1, ^bb4]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb1:
  "cf.br"() [^bb5] : () -> ()
^bb2:
  %use = "arith.addi"(%value, %value) : (i32, i32) -> i32
  "cf.br"() [^bb1] : () -> ()
^bb3:
  "cf.cond_br"(%cond) [^bb2, ^bb4]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb4:
  %value = "arith.constant"() <{value = 1 : i32}> : () -> i32
  "cf.cond_br"(%cond) [^bb2, ^bb5]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb5:
  "cf.cond_br"(%cond) [^bb3, ^bb5]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
}) : () -> ()

// CHECK: arith.addi: operand #0 does not dominate this use
