// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A sample of the `gmir` fold table, whose entries apply when only some
// operands are known. `GMIR.tryFold_sound` proves every entry; these check
// that each kind of fold reaches the IR, including the multi-result ones.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @add_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_add"
      // CHECK: "func.return"(%[[X]])
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_add"(%x, %c1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i32, sym_name = "and_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @and_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_and"
      // CHECK: %[[R:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}>
      // CHECK-NOT: "gmir.g_and"
      // CHECK: "func.return"(%[[R]])
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_and"(%x, %c1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i32, sym_name = "srem_ones"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @srem_ones(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_srem"
      // CHECK: %[[R:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}>
      // CHECK-NOT: "gmir.g_srem"
      // CHECK: "func.return"(%[[R]])
      %c1 = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
      %r = "gmir.g_srem"(%x, %c1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i32, sym_name = "shl_zero_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @shl_zero_lhs(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_shl"
      // CHECK: %[[R:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}>
      // CHECK-NOT: "gmir.g_shl"
      // CHECK: "func.return"(%[[R]])
      %c0 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_shl"(%c0, %x) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i32, sym_name = "sub_zero_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @sub_zero_lhs(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK: "gmir.g_sub"
      %c0 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_sub"(%c0, %x) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i1, sym_name = "icmp_ult_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @icmp_ult_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_icmp"
      // CHECK: %[[R:.*]] = "gmir.g_constant"() <{"value" = false}>
      // CHECK-NOT: "gmir.g_icmp"
      // CHECK: "func.return"(%[[R]])
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_icmp"(%x, %c1) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
      "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> i1, sym_name = "icmp_eq_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @icmp_eq_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK: "gmir.g_icmp"
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r = "gmir.g_icmp"(%x, %c1) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
      "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "uaddo_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @uaddo_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK-NOT: "gmir.g_uaddo"
      // CHECK: %[[O:.*]] = "gmir.g_constant"() <{"value" = false}>
      // CHECK-NOT: "gmir.g_uaddo"
      // CHECK: "func.return"(%[[X]], %[[O]])
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %r, %o = "gmir.g_uaddo"(%x, %c1) : (i32, i32) -> (i32, i1)
      "func.return"(%r, %o) : (i32, i1) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "uadde_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @uadde_zero(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK: %[[O:.*]] = "gmir.g_constant"() <{"value" = false}>
      // CHECK-NOT: "gmir.g_uadde"
      // CHECK: "func.return"(%[[X]], %[[O]])
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %c2 = "gmir.g_constant"() <{value = 0 : i1}> : () -> i1
      %r, %o = "gmir.g_uadde"(%x, %c1, %c2) : (i32, i32, i1) -> (i32, i1)
      "func.return"(%r, %o) : (i32, i1) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "uadde_carry"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: func.func @uadde_carry(
      // CHECK-SAME: %[[X:[^:]*]]: i32)
      // CHECK: "gmir.g_uadde"
      %c1 = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
      %c2 = "gmir.g_constant"() <{value = 1 : i1}> : () -> i1
      %r, %o = "gmir.g_uadde"(%x, %c1, %c2) : (i32, i32, i1) -> (i32, i1)
      "func.return"(%r, %o) : (i32, i1) -> ()
  }) : () -> ()
}) : () -> ()
