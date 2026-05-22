// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %two = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %a = "test.test"() : () -> i32
    // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "test.test"() : () -> i32

    %mul_zero = "llvm.mul"(%a, %zero) : (i32, i32) -> i32
    %mul_two = "llvm.mul"(%a, %two) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32

    "test.test"(%mul_zero, %mul_two) : (i32, i32) -> ()
    // CHECK-NEXT: "test.test"(%{{.*}}, %{{.*}}) : (i32, i32) -> ()

}) : () -> ()
