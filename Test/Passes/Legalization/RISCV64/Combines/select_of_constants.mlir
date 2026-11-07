// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

// The other zero/one, all-ones/zero, and power-of-two folds are covered by
// select_into_binop.mlir, where they also check that the two optimizations chain.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "select_of_constants"}> ({
  ^bb0(%c: i1):
    %one = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %zero = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
    // c ? 1 : 0 -> zext c.
    // CHECK-LABEL: func.func @select_of_constants
    // CHECK-SAME: (%[[C:.*]]: i1)
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %one, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1) -> (), sym_name = "select_succ"}> ({
  ^bb0(%c: i1):
    %t = "gmir.g_constant"() <{value = -128 : i8}> : () -> i8
    %f = "gmir.g_constant"() <{value = 127 : i8}> : () -> i8
    // c ? F + 1 : F -> add (zext c), F, including wraparound.
    // CHECK-LABEL: func.func @select_succ
    // CHECK-SAME: (%[[C:.*]]: i1)
    // CHECK-NEXT: %[[F:.*]] = "gmir.g_constant"() <{"value" = 127 : i8}> : () -> i8
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_zext"(%[[C]]) : (i1) -> i8
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[E]], %[[F]]) : (i8, i8) -> i8
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %t, %f) : (i1, i8, i8) -> i8
    "test.test"(%r) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1) -> (), sym_name = "select_pred"}> ({
  ^bb0(%c: i1):
    %t = "gmir.g_constant"() <{value = 127 : i8}> : () -> i8
    %f = "gmir.g_constant"() <{value = -128 : i8}> : () -> i8
    // c ? F - 1 : F -> add (sext c), F, including wraparound.
    // CHECK-LABEL: func.func @select_pred
    // CHECK-SAME: (%[[C:.*]]: i1)
    // CHECK-NEXT: %[[F:.*]] = "gmir.g_constant"() <{"value" = -128 : i8}> : () -> i8
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i8
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[E]], %[[F]]) : (i8, i8) -> i8
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %t, %f) : (i1, i8, i8) -> i8
    "test.test"(%r) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1) -> (), sym_name = "select_allones_const"}> ({
  ^bb0(%c: i1):
    %ones = "gmir.g_constant"() <{value = 255 : i8}> : () -> i8
    %f = "gmir.g_constant"() <{value = 42 : i8}> : () -> i8
    // c ? -1 : F -> or (sext c), F. Recognize all ones in unsigned spelling.
    // CHECK-LABEL: func.func @select_allones_const
    // CHECK-SAME: (%[[C:.*]]: i1)
    // CHECK-NEXT: %[[F:.*]] = "gmir.g_constant"() <{"value" = 42 : i8}> : () -> i8
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[C]]) : (i1) -> i8
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[E]], %[[F]]) : (i8, i8) -> i8
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %ones, %f) : (i1, i8, i8) -> i8
    "test.test"(%r) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1) -> (), sym_name = "select_const_allones"}> ({
  ^bb0(%c: i1):
    %t = "gmir.g_constant"() <{value = 42 : i8}> : () -> i8
    %ones = "gmir.g_constant"() <{value = -1 : i8}> : () -> i8
    // c ? T : -1 -> or (sext (not c)), T.
    // CHECK-LABEL: func.func @select_const_allones
    // CHECK-SAME: (%[[C:.*]]: i1)
    // CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = true}> : () -> i1
    // CHECK-NEXT: %[[N:.*]] = "gmir.g_xor"(%[[C]], %[[ONES]]) : (i1, i1) -> i1
    // CHECK-NEXT: %[[E:.*]] = "gmir.g_sext"(%[[N]]) : (i1) -> i8
    // CHECK-NEXT: %[[T:.*]] = "gmir.g_constant"() <{"value" = 42 : i8}> : () -> i8
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[E]], %[[T]]) : (i8, i8) -> i8
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %t, %ones) : (i1, i8, i8) -> i8
    "test.test"(%r) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
