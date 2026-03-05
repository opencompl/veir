// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %two = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32

    // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "test.test"() : () -> i32

    %mul_zero = "llvm.mul"(%x, %zero) : (i32, i32) -> i32
    %mul_two = "llvm.mul"(%x, %two) : (i32, i32) -> i32

    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32

    "test.test"(%mul_zero, %mul_two) : (i32, i32) -> ()

    // CHECK-NEXT: "test.test"(%{{.*}}, %{{.*}}) : (i32, i32) -> ()

}) : () -> ()
