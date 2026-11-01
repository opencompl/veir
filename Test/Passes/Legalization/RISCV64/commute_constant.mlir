// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Commutation keeps flags and every result, recognizes constants from other
// dialects, and does not swap two constants or already-canonical operands.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "commute"}> ({
    %x = "test.test"() : () -> i64
    %c = "gmir.g_constant"() <{value = 5 : i64}> : () -> i64
    %d = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    // CHECK: %[[X:.*]] = "test.test"() : () -> i64
    // CHECK: %[[C:.*]] = "gmir.g_constant"() <{"value" = 5 : i64}>
    // CHECK: %[[D:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i64}>

    %add = "gmir.g_add"(%c, %x) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[ADD:.*]] = "gmir.g_add"(%[[X]], %[[C]]) <{"overflowFlags" = 3 : i32}>
    %mul = "gmir.g_mul"(%d, %x) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[MUL:.*]] = "gmir.g_mul"(%[[X]], %[[D]]) <{"overflowFlags" = 1 : i32}>
    %sum, %carry = "gmir.g_uaddo"(%c, %x) : (i64, i64) -> (i64, i1)
    // CHECK-NEXT: %[[PAIR:.*]]:2 = "gmir.g_uaddo"(%[[X]], %[[C]]) : (i64, i64) -> (i64, i1)
    %both = "gmir.g_mul"(%c, %d) : (i64, i64) -> i64
    // CHECK-NEXT: %[[BOTH:.*]] = "gmir.g_mul"(%[[C]], %[[D]])
    %right = "gmir.g_xor"(%x, %c) : (i64, i64) -> i64
    // CHECK-NEXT: %[[RIGHT:.*]] = "gmir.g_xor"(%[[X]], %[[C]])
    %sub = "gmir.g_sub"(%c, %x) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SUB:.*]] = "gmir.g_sub"(%[[C]], %[[X]])
    "test.test"(%add, %mul, %sum, %carry, %both, %right, %sub) : (i64, i64, i64, i1, i64, i64, i64) -> ()
    // CHECK-NEXT: "test.test"(%[[ADD]], %[[MUL]], %[[PAIR]]#0, %[[PAIR]]#1, %[[BOTH]], %[[RIGHT]], %[[SUB]])
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
