// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "multi_result"}> ({
  ^bb0(%a : i32, %b : i32):
    // CSE commuted addui_extended operations and redirect both results.
    %sum0, %overflow0 = "arith.addui_extended"(%a, %b) : (i32, i32) -> (i32, i1)
    %sum1, %overflow1 = "arith.addui_extended"(%b, %a) : (i32, i32) -> (i32, i1)

    // Rewriting %sum1 to %sum0 also exposes this single-result CSE.
    %use0 = "arith.addi"(%sum0, %a) : (i32, i32) -> i32
    %use1 = "arith.addi"(%sum1, %a) : (i32, i32) -> i32
    "test.test"(%sum0, %overflow0, %sum1, %overflow1, %use0, %use1)
      : (i32, i1, i32, i1, i32, i32) -> ()

    // Signed and unsigned extended multiplies each CSE across commuted
    // operands, but their distinct opcodes keep them from merging together.
    %slo0, %shi0 = "arith.mulsi_extended"(%a, %b) : (i32, i32) -> (i32, i32)
    %slo1, %shi1 = "arith.mulsi_extended"(%b, %a) : (i32, i32) -> (i32, i32)
    %ulo0, %uhi0 = "arith.mului_extended"(%a, %b) : (i32, i32) -> (i32, i32)
    %ulo1, %uhi1 = "arith.mului_extended"(%b, %a) : (i32, i32) -> (i32, i32)
    "test.test"(%slo0, %shi0, %slo1, %shi1, %ulo0, %uhi0, %ulo1, %uhi1)
      : (i32, i32, i32, i32, i32, i32, i32, i32) -> ()

    // subui_extended is not commutative, so only the repeat with identical
    // operand order CSEs; the commuted one survives.
    %diff0, %borrow0 = "arith.subui_extended"(%a, %b) : (i32, i32) -> (i32, i1)
    %diff1, %borrow1 = "arith.subui_extended"(%a, %b) : (i32, i32) -> (i32, i1)
    %diff2, %borrow2 = "arith.subui_extended"(%b, %a) : (i32, i32) -> (i32, i1)
    "test.test"(%diff0, %borrow0, %diff1, %borrow1, %diff2, %borrow2)
      : (i32, i1, i32, i1, i32, i1) -> ()
    "func.return"() : () -> ()

    // CHECK-LABEL: func.func @multi_result(
    // CHECK:      %[[ADD:.*]]:2 = "arith.addui_extended"(%[[A:[^ ]*]], %[[B:[^ ]*]]) : (i32, i32) -> (i32, i1)
    // CHECK-NEXT: %[[USE:.*]] = "arith.addi"(%[[ADD]]#0, %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD]]#0, %[[ADD]]#1, %[[ADD]]#0, %[[ADD]]#1, %[[USE]], %[[USE]])
    // CHECK-NEXT: %[[SMUL:.*]]:2 = "arith.mulsi_extended"(%[[A]], %[[B]])
    // CHECK-SAME:   : (i32, i32) -> (i32, i32)
    // CHECK-NEXT: %[[UMUL:.*]]:2 = "arith.mului_extended"(%[[A]], %[[B]])
    // CHECK-SAME:   : (i32, i32) -> (i32, i32)
    // CHECK-NEXT: "test.test"(%[[SMUL]]#0, %[[SMUL]]#1,
    // CHECK-SAME: %[[SMUL]]#0, %[[SMUL]]#1, %[[UMUL]]#0, %[[UMUL]]#1,
    // CHECK-SAME: %[[UMUL]]#0, %[[UMUL]]#1)
    // CHECK-NEXT: %[[SUB:.*]]:2 = "arith.subui_extended"(%[[A]], %[[B]]) : (i32, i32) -> (i32, i1)
    // CHECK-NEXT: %[[RSUB:.*]]:2 = "arith.subui_extended"(%[[B]], %[[A]]) : (i32, i32) -> (i32, i1)
    // CHECK-NEXT: "test.test"(%[[SUB]]#0, %[[SUB]]#1, %[[SUB]]#0, %[[SUB]]#1,
    // CHECK-SAME: %[[RSUB]]#0, %[[RSUB]]#1)
    // CHECK-NEXT: "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
