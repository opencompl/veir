// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    // --- DeMorgan patterns ---
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %a = "test.test"() : () -> i32
    // CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32

    // Negative: xor(xor(a, -1), -7) is not ~~a -- outer constant is not -1.
    %m7 = "llvm.mlir.constant"() <{ "value" = -7 : i32 }> : () -> i32
    %na_neg = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %not_nna = "llvm.xor"(%na_neg, %m7) : (i32, i32) -> i32
    "test.test"(%not_nna) : (i32) -> ()
    // CHECK-NEXT: %[[M7:.*]] = "llvm.mlir.constant"() <{"value" = -7 : i32}> : () -> i32
    // CHECK-NEXT: %[[NA_NEG:.*]] = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[NEG_RES:.*]] = "llvm.xor"(%[[NA_NEG]], %[[M7]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[NEG_RES]]) : (i32) -> ()

}) : () -> ()
