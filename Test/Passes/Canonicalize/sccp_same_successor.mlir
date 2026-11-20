// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Successor slots must have independent liveness even when they target the same block.

"builtin.module"() ({
  "func.func"() <{sym_name = "same_successor_true", function_type = () -> i32}> ({
    // CHECK-LABEL: func.func @same_successor_true
    // CHECK: %[[TRUE_VALUE:.*]] = "arith.constant"() <{"value" = 11 : i32}>
    // CHECK: "func.return"(%[[TRUE_VALUE]])
    %condition = "arith.constant"() <{value = true}> : () -> i1
    %a = "arith.constant"() <{value = 11 : i32}> : () -> i32
    %b = "arith.constant"() <{value = 22 : i32}> : () -> i32
    "cf.cond_br"(%condition, %a, %b) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^join(%x : i32):
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "same_successor_false", function_type = () -> i32}> ({
    // CHECK-LABEL: func.func @same_successor_false
    // CHECK: %[[FALSE_VALUE:.*]] = "arith.constant"() <{"value" = 22 : i32}>
    // CHECK: "func.return"(%[[FALSE_VALUE]])
    %condition = "arith.constant"() <{value = false}> : () -> i1
    %a = "arith.constant"() <{value = 11 : i32}> : () -> i32
    %b = "arith.constant"() <{value = 22 : i32}> : () -> i32
    "cf.cond_br"(%condition, %a, %b) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^join(%x : i32):
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "same_successor_unknown", function_type = (i1) -> i32}> ({
  ^entry(%condition : i1):
    // CHECK-LABEL: func.func @same_successor_unknown
    // CHECK: "cf.cond_br"
    // CHECK: ^{{[0-9]+}}(%[[ARG:.*]] : i32):
    // CHECK-NEXT: "func.return"(%[[ARG]])
    %a = "arith.constant"() <{value = 11 : i32}> : () -> i32
    %b = "arith.constant"() <{value = 22 : i32}> : () -> i32
    "cf.cond_br"(%condition, %a, %b) [^join, ^join]
      <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^join(%x : i32):
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
