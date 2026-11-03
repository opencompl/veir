// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({

  // mod_arith.add and mod_arith.mul are commutative, so commuted operands
  // merge; mod_arith.sub is not.
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> (), sym_name = "binops"}> ({
  ^bb0(%a : !mod_arith.int<7 : i32>, %b : !mod_arith.int<7 : i32>):
    %add0 = "mod_arith.add"(%a, %b) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %add1 = "mod_arith.add"(%b, %a) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %mul0 = "mod_arith.mul"(%a, %b) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %mul1 = "mod_arith.mul"(%b, %a) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %sub0 = "mod_arith.sub"(%a, %b) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %sub1 = "mod_arith.sub"(%a, %b) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %sub2 = "mod_arith.sub"(%b, %a) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    "test.test"(%add0, %add1, %mul0, %mul1, %sub0, %sub1, %sub2) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @binops(
    // CHECK:      %[[ADD:.*]] = "mod_arith.add"(%[[A:[^ ]*]], %[[B:[^ ]*]])
    // CHECK-NEXT: %[[MUL:.*]] = "mod_arith.mul"(%[[A]], %[[B]])
    // CHECK-NEXT: %[[SUB:.*]] = "mod_arith.sub"(%[[A]], %[[B]])
    // CHECK-NEXT: %[[SUBR:.*]] = "mod_arith.sub"(%[[B]], %[[A]])
    // CHECK-NEXT: "test.test"(%[[ADD]], %[[ADD]], %[[MUL]], %[[MUL]], %[[SUB]], %[[SUB]], %[[SUBR]])
  }) : () -> ()

  // The modulus lives in the type, so equivalent-looking ops on different
  // moduli must not merge. Same for mod_arith.constant.
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<11 : i32>, !mod_arith.int<11 : i32>) -> (), sym_name = "moduli"}> ({
  ^bb0(%a7 : !mod_arith.int<7 : i32>, %b7 : !mod_arith.int<7 : i32>, %a11 : !mod_arith.int<11 : i32>, %b11 : !mod_arith.int<11 : i32>):
    %s7 = "mod_arith.add"(%a7, %b7) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    %s11 = "mod_arith.add"(%a11, %b11) : (!mod_arith.int<11 : i32>, !mod_arith.int<11 : i32>) -> !mod_arith.int<11 : i32>
    %c3_7a = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<7 : i32>
    %c3_7b = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<7 : i32>
    %c5_7 = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<7 : i32>
    %c3_11 = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<11 : i32>
    "test.test"(%s7, %s11, %c3_7a, %c3_7b, %c5_7, %c3_11) : (!mod_arith.int<7 : i32>, !mod_arith.int<11 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<11 : i32>) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @moduli(
    // CHECK:      %[[S7:.*]] = "mod_arith.add"({{.*}}) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
    // CHECK-NEXT: %[[S11:.*]] = "mod_arith.add"({{.*}}) : (!mod_arith.int<11 : i32>, !mod_arith.int<11 : i32>) -> !mod_arith.int<11 : i32>
    // CHECK-NEXT: %[[C3_7:.*]] = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<7 : i32>
    // CHECK-NEXT: %[[C5_7:.*]] = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<7 : i32>
    // CHECK-NEXT: %[[C3_11:.*]] = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<11 : i32>
    // CHECK-NEXT: "test.test"(%[[S7]], %[[S11]], %[[C3_7]], %[[C3_7]], %[[C5_7]], %[[C3_11]])
  }) : () -> ()

}) : () -> ()
