// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32
    // CHECK: %[[ONE:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

    // mul x * 1 => x
    %mul_one = "llvm.mul"(%x, %one) : (i32, i32) -> i32
    "test.test"(%mul_one) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

}) : () -> ()
