// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    // --- DeMorgan patterns ---
    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %a = "test.test"() : () -> i32
    // CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32

    // ~~a => a
    %na0 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %nna = "llvm.xor"(%na0, %m1) : (i32, i32) -> i32
    "test.test"(%nna) : (i32) -> ()
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[A]]) : (i32) -> ()

}) : () -> ()
