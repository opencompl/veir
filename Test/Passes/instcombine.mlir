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

    // --- Identity and annihilation patterns ---

    %one = "llvm.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %y = "test.test"() : () -> i32

    // mul x * 1 => x
    %mul_one = "llvm.mul"(%y, %one) : (i32, i32) -> i32

    // add x + 0 => x
    %add_zero = "llvm.add"(%y, %zero) : (i32, i32) -> i32

    // sub x - 0 => x
    %sub_zero = "llvm.sub"(%y, %zero) : (i32, i32) -> i32

    // sub x - x => 0
    %sub_self = "llvm.sub"(%y, %y) : (i32, i32) -> i32

    // and x & x => x
    %and_self = "llvm.and"(%y, %y) : (i32, i32) -> i32

    // and x & 0 => 0
    %and_zero = "llvm.and"(%y, %zero) : (i32, i32) -> i32

    // or x | 0 => x
    %or_zero = "llvm.or"(%y, %zero) : (i32, i32) -> i32

    // or x | x => x
    %or_self = "llvm.or"(%y, %y) : (i32, i32) -> i32

    // xor x ^ 0 => x
    %xor_zero = "llvm.xor"(%y, %zero) : (i32, i32) -> i32

    // xor x ^ x => 0
    %xor_self = "llvm.xor"(%y, %y) : (i32, i32) -> i32

    // All identity rewrites (x+0, x*1, x-0, x|0, x^0, x&x, x|x) should
    // eliminate the op and forward the input. Annihilation rewrites (x-x,
    // x&0, x^x) should produce a constant 0.

    // CHECK-NEXT: %[[ONE:.*]] = "llvm.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %[[Y:.*]] = "test.test"() : () -> i32
    // CHECK-NEXT: %[[ZERO1:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[ZERO2:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[ZERO3:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32

    "test.test"(%mul_one, %add_zero, %sub_zero, %sub_self, %and_self, %and_zero, %or_zero, %or_self, %xor_zero, %xor_self) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()

    // CHECK-NEXT: "test.test"(%[[Y]], %[[Y]], %[[Y]], %[[ZERO1]], %[[Y]], %[[ZERO2]], %[[Y]], %[[Y]], %[[Y]], %[[ZERO3]]) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()

}) : () -> ()
