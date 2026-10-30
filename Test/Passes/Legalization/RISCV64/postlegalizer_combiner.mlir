// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
    %x = "test.test"() : () -> i64
    %y = "test.test"() : () -> i64
    %c = "gmir.g_constant"() <{value = 5 : i64}> : () -> i64
    %d = "gmir.g_constant"() <{value = 7 : i64}> : () -> i64
    // A constant on the left of a commutative operation moves to the right.
    // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = 5 : i64}>
    // CHECK-NEXT: %[[D:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}>
    // CHECK-NEXT: "gmir.g_add"(%{{.*}}, %[[C]])
    %add = "gmir.g_add"(%c, %x) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_and"(%{{.*}}, %[[C]])
    %and = "gmir.g_and"(%c, %y) : (i64, i64) -> i64
    // A constant that is already on the right, or an operation with two constants, stays.
    // CHECK-NEXT: "gmir.g_xor"(%{{.*}}, %[[C]])
    %xor = "gmir.g_xor"(%x, %c) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_or"(%[[C]], %[[D]])
    %or = "gmir.g_or"(%c, %d) : (i64, i64) -> i64
    // Subtraction of a constant becomes the addition of the negated constant.
    // CHECK:      %[[NEG:.*]] = "gmir.g_constant"() <{"value" = -5 : i64}>
    // CHECK-NEXT: "gmir.g_add"(%{{.*}}, %[[NEG]]) : (i64, i64) -> i64
    %sub = "gmir.g_sub"(%x, %c) : (i64, i64) -> i64
    "test.test"(%add, %and, %xor, %or, %sub) : (i64, i64, i64, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
