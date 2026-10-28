// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i1) -> (), sym_name = "main"}> ({
  ^bb0(%a: i64, %b: i64, %c: i1):
    // CHECK: func.func @main(%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i1) {

    // `g_uaddo` carries when the sum is less than either operand.
    %uaddo, %uaddo_carry = "gmir.g_uaddo"(%a, %b) : (i64, i64) -> (i64, i1)
    // CHECK-NEXT: %[[UADDO:.*]] = "gmir.g_add"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDO_CMP:.*]] = "gmir.g_icmp"(%[[UADDO]], %[[B]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDO_CARRY:.*]] = "gmir.g_trunc"(%[[UADDO_CMP]]) : (i64) -> i1

    // `g_uadde` also carries when the carry-in wraps the sum around to zero.
    %uadde, %uadde_carry = "gmir.g_uadde"(%a, %b, %c) : (i64, i64, i1) -> (i64, i1)
    // CHECK-NEXT: %[[UADDE_TMP:.*]] = "gmir.g_add"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_CMP:.*]] = "gmir.g_icmp"(%[[UADDE_TMP]], %[[A]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_EXT:.*]] = "gmir.g_anyext"(%[[C]]) : (i1) -> i64
    // CHECK-NEXT: %[[UADDE_MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[UADDE_ZEXT:.*]] = "gmir.g_and"(%[[UADDE_EXT]], %[[UADDE_MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE:.*]] = "gmir.g_add"(%[[UADDE_TMP]], %[[UADDE_ZEXT]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[UADDE_EQ:.*]] = "gmir.g_icmp"(%[[UADDE]], %[[UADDE_ZERO]]) <{"predicate" = 0 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_C:.*]] = "gmir.g_anyext"(%[[C]]) : (i1) -> i64
    // CHECK-NEXT: %[[UADDE_AND:.*]] = "gmir.g_and"(%[[UADDE_EQ]], %[[UADDE_C]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_OR:.*]] = "gmir.g_or"(%[[UADDE_CMP]], %[[UADDE_AND]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[UADDE_CARRY:.*]] = "gmir.g_trunc"(%[[UADDE_OR]]) : (i64) -> i1

    // `g_usubo` borrows when `a` is less than `b`.
    %usubo, %usubo_borrow = "gmir.g_usubo"(%a, %b) : (i64, i64) -> (i64, i1)
    // CHECK-NEXT: %[[USUBO:.*]] = "gmir.g_sub"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBO_CMP:.*]] = "gmir.g_icmp"(%[[A]], %[[B]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBO_BORROW:.*]] = "gmir.g_trunc"(%[[USUBO_CMP]]) : (i64) -> i1

    // `g_usube` also borrows when the borrow-in is subtracted from a zero difference.
    %usube, %usube_borrow = "gmir.g_usube"(%a, %b, %c) : (i64, i64, i1) -> (i64, i1)
    // CHECK-NEXT: %[[USUBE_TMP:.*]] = "gmir.g_sub"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_CMP:.*]] = "gmir.g_icmp"(%[[USUBE_TMP]], %[[A]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_EXT:.*]] = "gmir.g_anyext"(%[[C]]) : (i1) -> i64
    // CHECK-NEXT: %[[USUBE_MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[USUBE_ZEXT:.*]] = "gmir.g_and"(%[[USUBE_EXT]], %[[USUBE_MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE:.*]] = "gmir.g_sub"(%[[USUBE_TMP]], %[[USUBE_ZEXT]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[USUBE_EQ:.*]] = "gmir.g_icmp"(%[[USUBE_TMP]], %[[USUBE_ZERO]]) <{"predicate" = 0 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_C:.*]] = "gmir.g_anyext"(%[[C]]) : (i1) -> i64
    // CHECK-NEXT: %[[USUBE_AND:.*]] = "gmir.g_and"(%[[USUBE_EQ]], %[[USUBE_C]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_OR:.*]] = "gmir.g_or"(%[[USUBE_CMP]], %[[USUBE_AND]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[USUBE_BORROW:.*]] = "gmir.g_trunc"(%[[USUBE_OR]]) : (i64) -> i1

    // CHECK-NEXT: "test.test"(%[[UADDO]], %[[UADDO_CARRY]], %[[UADDE]], %[[UADDE_CARRY]], %[[USUBO]], %[[USUBO_BORROW]], %[[USUBE]], %[[USUBE_BORROW]])
    "test.test"(%uaddo, %uaddo_carry, %uadde, %uadde_carry, %usubo, %usubo_borrow, %usube, %usube_borrow) : (i64, i1, i64, i1, i64, i1, i64, i1) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
