// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "chains_into_constants"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 16 : i32}> : () -> i32
    // c ? (shl nsw nuw x, 16) : x -> shl x, (shl (zext c), 4), dropping the flags.
    // CHECK-LABEL: func.func @chains_into_constants
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%[[X]], %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %shl = "gmir.g_shl"(%x, %k) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %shl, %x) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_lshr_swapped"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 16 : i32}> : () -> i32
    // c ? x : (lshr exact x, 16) -> lshr x, (shl (zext (not c)), 4).
    // CHECK-LABEL: func.func @select_into_lshr_swapped
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[N:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[N]]) : (i1) -> i32
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 4 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "gmir.g_shl"(%[[E]], %[[K]]) : (i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_lshr"(%[[X]], %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %shift = "gmir.g_lshr"(%x, %k) <{isExact}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %x, %shift) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_ashr"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    // c ? (ashr exact x, 1) : x -> ashr x, (zext c).
    // CHECK-LABEL: func.func @select_into_ashr
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_ashr"(%[[X]], %[[E]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %shift = "gmir.g_ashr"(%x, %k) <{isExact}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %shift, %x) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_sub"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
    // c ? (sub nsw nuw x, -1) : x -> sub x, (sext c).
    // CHECK-LABEL: func.func @select_into_sub
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sub"(%[[X]], %[[E]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %sub = "gmir.g_sub"(%x, %k) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %sub, %x) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_add_swapped"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    // c ? x : (add nsw nuw x, 1) -> add x, (zext (not c)).
    // CHECK-LABEL: func.func @select_into_add_swapped
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[N:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[N]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[X]], %[[E]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %add = "gmir.g_add"(%x, %k) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %x, %add) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_or_swapped"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
    // c ? x : (or disjoint x, -1) -> or x, (sext (not c)).
    // CHECK-LABEL: func.func @select_into_or_swapped
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[N:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[N]]) : (i1) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[X]], %[[E]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %or = "gmir.g_or"(%x, %k) <{isDisjoint}> : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %x, %or) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "select_into_xor_swapped"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 6 : i32}> : () -> i32
    // c ? x : (xor x, 6) -> xor x, (c ? 0 : 6); this inner select does not fold.
    // CHECK-LABEL: func.func @select_into_xor_swapped
    // CHECK-SAME: (%[[C:.*]]: i1, %[[X:.*]]: i32)
    // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 6 : i32}> : () -> i32
    // CHECK-NEXT: %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[A:.*]] = "gmir.g_select"(%[[C]], %[[Z]], %[[K]]) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_xor"(%[[X]], %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %xor = "gmir.g_xor"(%x, %k) : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %x, %xor) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
