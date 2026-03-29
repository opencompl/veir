// RUN: veir-opt %s -p=instcombine | filecheck %s

"builtin.module"() ({
^bb0():
    %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
    %two = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %a = "test.test"() : () -> i32

    // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "test.test"() : () -> i32

    %mul_zero = "llvm.mul"(%a, %zero) : (i32, i32) -> i32
    %mul_two = "llvm.mul"(%a, %two) : (i32, i32) -> i32

    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32

    "test.test"(%mul_zero, %mul_two) : (i32, i32) -> ()

    // CHECK-NEXT: "test.test"(%{{.*}}, %{{.*}}) : (i32, i32) -> ()

    // --- Identity and annihilation patterns ---

    %one = "llvm.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32

    // CHECK-NEXT: %[[ONE:.*]] = "llvm.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %[[X:.*]] = "test.test"() : () -> i32

    // mul x * 1 => x
    %mul_one = "llvm.mul"(%x, %one) : (i32, i32) -> i32
    "test.test"(%mul_one) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // add x + 0 => x
    %add_zero = "llvm.add"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%add_zero) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // sub x - 0 => x
    %sub_zero = "llvm.sub"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%sub_zero) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // sub x - x => 0
    %sub_self = "llvm.sub"(%x, %x) : (i32, i32) -> i32
    "test.test"(%sub_self) : (i32) -> ()
    // CHECK-NEXT: %[[SUB_ZERO:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[SUB_ZERO]]) : (i32) -> ()

    // and x & x => x
    %and_self = "llvm.and"(%x, %x) : (i32, i32) -> i32
    "test.test"(%and_self) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // and x & 0 => 0
    %and_zero = "llvm.and"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%and_zero) : (i32) -> ()
    // CHECK-NEXT: %[[AND_ZERO:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[AND_ZERO]]) : (i32) -> ()

    // or x | 0 => x
    %or_zero = "llvm.or"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%or_zero) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // or x | x => x
    %or_self = "llvm.or"(%x, %x) : (i32, i32) -> i32
    "test.test"(%or_self) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // xor x ^ 0 => x
    %xor_zero = "llvm.xor"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%xor_zero) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // xor x ^ x => 0
    %xor_self = "llvm.xor"(%x, %x) : (i32, i32) -> i32
    "test.test"(%xor_self) : (i32) -> ()
    // CHECK-NEXT: %[[XOR_ZERO:.*]] = "llvm.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[XOR_ZERO]]) : (i32) -> ()

}) : () -> ()
