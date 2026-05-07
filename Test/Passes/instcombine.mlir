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

    // --- Identity and annihilation patterns ---

    %one = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %x = "test.test"() : () -> i32

    // CHECK-NEXT: %[[ONE:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
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
    // CHECK-NEXT: %[[SUB_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[SUB_ZERO]]) : (i32) -> ()

    // and x & x => x
    %and_self = "llvm.and"(%x, %x) : (i32, i32) -> i32
    "test.test"(%and_self) : (i32) -> ()
    // CHECK-NEXT: "test.test"(%[[X]]) : (i32) -> ()

    // and x & 0 => 0
    %and_zero = "llvm.and"(%x, %zero) : (i32, i32) -> i32
    "test.test"(%and_zero) : (i32) -> ()
    // CHECK-NEXT: %[[AND_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
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
    // CHECK-NEXT: %[[XOR_ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: "test.test"(%[[XOR_ZERO]]) : (i32) -> ()

    // --- DeMorgan patterns ---

    %m1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %a = "test.test"() : () -> i32
    %b = "test.test"() : () -> i32

    // CHECK-NEXT: %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> i32
    // CHECK-NEXT: %[[B:.*]] = "test.test"() : () -> i32

    // ~~a => a
    %na0 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %nna = "llvm.xor"(%na0, %m1) : (i32, i32) -> i32
    "test.test"(%nna) : (i32) -> ()
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[A]]) : (i32) -> ()

    // Negative: xor(xor(a, -1), -7) is not ~~a -- outer constant is not -1.
    %m7 = "llvm.mlir.constant"() <{ "value" = -7 : i32 }> : () -> i32
    %na_neg = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %not_nna = "llvm.xor"(%na_neg, %m7) : (i32, i32) -> i32
    "test.test"(%not_nna) : (i32) -> ()
    // CHECK-NEXT: %[[M7:.*]] = "llvm.mlir.constant"() <{"value" = -7 : i32}> : () -> i32
    // CHECK-NEXT: %[[NA_NEG:.*]] = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[NEG_RES:.*]] = "llvm.xor"(%[[NA_NEG]], %[[M7]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[NEG_RES]]) : (i32) -> ()

    // ~(~a & ~b) => a | b
    %na1 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %nb1 = "llvm.xor"(%b, %m1) : (i32, i32) -> i32
    %and1 = "llvm.and"(%na1, %nb1) : (i32, i32) -> i32
    %demorgan_or = "llvm.xor"(%and1, %m1) : (i32, i32) -> i32
    "test.test"(%demorgan_or) : (i32) -> ()
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[B]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[OR:.*]] = "llvm.or"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[OR]]) : (i32) -> ()

    // ~(~a | ~b) => a & b
    %na2 = "llvm.xor"(%a, %m1) : (i32, i32) -> i32
    %nb2 = "llvm.xor"(%b, %m1) : (i32, i32) -> i32
    %or2 = "llvm.or"(%na2, %nb2) : (i32, i32) -> i32
    %demorgan_and = "llvm.xor"(%or2, %m1) : (i32, i32) -> i32
    "test.test"(%demorgan_and) : (i32) -> ()
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[A]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.xor"(%[[B]], %[[M1]]) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[AND:.*]] = "llvm.and"(%[[A]], %[[B]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[AND]]) : (i32) -> ()

}) : () -> ()
