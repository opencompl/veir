// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64, i64) -> (), sym_name = "main"}> ({
  ^bb0(%a_lo: i64, %a_hi: i64, %b_lo: i64, %b_hi: i64):
    // CHECK: func.func @main(%[[A_LO:.*]]: i64, %[[A_HI:.*]]: i64, %[[B_LO:.*]]: i64, %[[B_HI:.*]]: i64) {
    %a = "gmir.g_merge_values"(%a_lo, %a_hi) : (i64, i64) -> i128
    %b = "gmir.g_merge_values"(%b_lo, %b_hi) : (i64, i64) -> i128

    // The `i128` `g_add` adds the halves, and the low half carries into the high half.
    %add = "gmir.g_add"(%a, %b) : (i128, i128) -> i128
    %add_lo, %add_hi = "gmir.g_unmerge_values"(%add) : (i128) -> (i64, i64)
    // CHECK-NEXT: %[[ADD_LO:.*]] = "gmir.g_add"(%[[A_LO]], %[[B_LO]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CARRY:.*]] = "gmir.g_icmp"(%[[ADD_LO]], %[[B_LO]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[ADD_HI_TMP:.*]] = "gmir.g_add"(%[[A_HI]], %[[B_HI]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CARRY_MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[CARRY_ZEXT:.*]] = "gmir.g_and"(%[[CARRY]], %[[CARRY_MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ADD_HI:.*]] = "gmir.g_add"(%[[ADD_HI_TMP]], %[[CARRY_ZEXT]]) : (i64, i64) -> i64

    // The `i128` `g_sub` subtracts the halves, and the low half borrows from the high half.
    %sub = "gmir.g_sub"(%a, %b) : (i128, i128) -> i128
    %sub_lo, %sub_hi = "gmir.g_unmerge_values"(%sub) : (i128) -> (i64, i64)
    // CHECK-NEXT: %[[SUB_LO:.*]] = "gmir.g_sub"(%[[A_LO]], %[[B_LO]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[BORROW:.*]] = "gmir.g_icmp"(%[[A_LO]], %[[B_LO]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[SUB_HI_TMP:.*]] = "gmir.g_sub"(%[[A_HI]], %[[B_HI]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[BORROW_MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[BORROW_ZEXT:.*]] = "gmir.g_and"(%[[BORROW]], %[[BORROW_MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SUB_HI:.*]] = "gmir.g_sub"(%[[SUB_HI_TMP]], %[[BORROW_ZEXT]]) : (i64, i64) -> i64

    // The `i65` `g_add` is widened to `i128`, then narrowed in the same way.
    %a_i65 = "gmir.g_trunc"(%a) : (i128) -> i65
    %b_i65 = "gmir.g_trunc"(%b) : (i128) -> i65
    %add_i65 = "gmir.g_add"(%a_i65, %b_i65) : (i65, i65) -> i65
    %add_i65_wide = "gmir.g_anyext"(%add_i65) : (i65) -> i128
    %add_i65_lo, %add_i65_hi = "gmir.g_unmerge_values"(%add_i65_wide) : (i128) -> (i64, i64)
    // CHECK-NEXT: %[[ADD65_LO:.*]] = "gmir.g_add"(%[[A_LO]], %[[B_LO]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CARRY65:.*]] = "gmir.g_icmp"(%[[ADD65_LO]], %[[B_LO]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: %[[ADD65_HI_TMP:.*]] = "gmir.g_add"(%[[A_HI]], %[[B_HI]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[CARRY65_MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[CARRY65_ZEXT:.*]] = "gmir.g_and"(%[[CARRY65]], %[[CARRY65_MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ADD65_HI:.*]] = "gmir.g_add"(%[[ADD65_HI_TMP]], %[[CARRY65_ZEXT]]) : (i64, i64) -> i64

    // CHECK-NEXT: "test.test"(%[[ADD_LO]], %[[ADD_HI]], %[[SUB_LO]], %[[SUB_HI]], %[[ADD65_LO]], %[[ADD65_HI]])
    "test.test"(%add_lo, %add_hi, %sub_lo, %sub_hi, %add_i65_lo, %add_i65_hi) : (i64, i64, i64, i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
