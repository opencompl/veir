// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// LLVM's `ptr_add_immed_chain` and `reassoc_ptradd` on `g_ptr_add`.

"builtin.module"() ({
  // `(p + 1) + 2` is `p + 3`.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "chain"}> ({
  ^bb0(%p: !llvm.ptr):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %q = "gmir.g_ptr_add"(%p, %c1) : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "gmir.g_ptr_add"(%q, %c2) : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%r) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @chain
  // CHECK-SAME:  (%[[P:.*]]: !llvm.ptr)
  // CHECK:       %[[C:.*]] = "gmir.g_constant"() <{"value" = 3 : i64}>
  // CHECK-NEXT:  %[[R:.*]] = "gmir.g_ptr_add"(%[[P]], %[[C]])
  // CHECK-NEXT:  "test.test"(%[[R]])

  // `(p + 1) + 2047` stays when `p + 1` has another use and a load would lose
  // its offset 2047, since 2048 does not fit.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "keep_offset"}> ({
  ^bb0(%p: !llvm.ptr):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 2047 : i64}> : () -> i64
    %q = "gmir.g_ptr_add"(%p, %c1) : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "gmir.g_ptr_add"(%q, %c2) : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "gmir.g_load"(%r) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i64
    "test.test"(%q, %v) : (!llvm.ptr, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @keep_offset
  // CHECK:       %[[Q:.*]] = "gmir.g_ptr_add"(%{{.*}}, %{{.*}})
  // CHECK-NEXT:  %[[R:.*]] = "gmir.g_ptr_add"(%[[Q]], %{{.*}})
  // CHECK-NEXT:  "gmir.g_load"(%[[R]])

  // Without a load or store, the offsets are combined.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "no_access"}> ({
  ^bb0(%p: !llvm.ptr):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 2047 : i64}> : () -> i64
    %q = "gmir.g_ptr_add"(%p, %c1) : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "gmir.g_ptr_add"(%q, %c2) : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%q, %r) : (!llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @no_access
  // CHECK-SAME:  (%[[P:.*]]: !llvm.ptr)
  // CHECK:       %[[C:.*]] = "gmir.g_constant"() <{"value" = 2048 : i64}>
  // CHECK-NEXT:  "gmir.g_ptr_add"(%[[P]], %[[C]])

  // When `p + 1` has no other use, the offsets are combined even for a load.
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "one_use"}> ({
  ^bb0(%p: !llvm.ptr):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 2047 : i64}> : () -> i64
    %q = "gmir.g_ptr_add"(%p, %c1) : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "gmir.g_ptr_add"(%q, %c2) : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "gmir.g_load"(%r) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i64
    "test.test"(%v) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @one_use
  // CHECK-SAME:  (%[[P:.*]]: !llvm.ptr)
  // CHECK:       %[[C:.*]] = "gmir.g_constant"() <{"value" = 2048 : i64}>
  // CHECK-NEXT:  "gmir.g_ptr_add"(%[[P]], %[[C]])

  // `(p + 1) + i` stays when `p + 1` has another use.
  "func.func"() <{function_type = (!llvm.ptr, i64) -> (), sym_name = "inner_lhs_uses"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %q = "gmir.g_ptr_add"(%p, %c1) : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "gmir.g_ptr_add"(%q, %i) : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%q, %r) : (!llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @inner_lhs_uses
  // CHECK-SAME:  (%[[P:.*]]: !llvm.ptr, %[[I:.*]]: i64)
  // CHECK:       %[[Q:.*]] = "gmir.g_ptr_add"(%[[P]], %{{.*}})
  // CHECK-NEXT:  %[[R:.*]] = "gmir.g_ptr_add"(%[[Q]], %[[I]])

  // `p + (i + 1)` becomes `(p + i) + 1`.
  "func.func"() <{function_type = (!llvm.ptr, i64) -> (), sym_name = "inner_rhs"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64):
    %c1 = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %a = "gmir.g_add"(%i, %c1) : (i64, i64) -> i64
    %r = "gmir.g_ptr_add"(%p, %a) : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%r) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @inner_rhs
  // CHECK-SAME:  (%[[P:.*]]: !llvm.ptr, %[[I:.*]]: i64)
  // CHECK:       %[[C:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}>
  // CHECK:       %[[Q:.*]] = "gmir.g_ptr_add"(%[[P]], %[[I]])
  // CHECK-NEXT:  %[[R:.*]] = "gmir.g_ptr_add"(%[[Q]], %[[C]])
  // CHECK-NEXT:  "test.test"(%[[R]])
}) : () -> ()
