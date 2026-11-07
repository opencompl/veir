// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "folds"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32

    // c ? (shl nuw x, K) : x -> shl x, (c ? K : 0). The flags are dropped.
    // CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 5 : i32}> : () -> i32
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[SEL:.*]] = "gmir.g_select"(%[[C:.*]], %[[K]], %[[ZERO]]) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_shl"(%[[X:.*]], %[[SEL]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %shl = "gmir.g_shl"(%x, %k) <{nuw}> : (i32, i32) -> i32
    %r0 = "gmir.g_select"(%c, %shl, %x) : (i1, i32, i32) -> i32
    "test.test"(%r0) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_lshr"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %lshr = "gmir.g_lshr"(%x, %k) : (i32, i32) -> i32
    %r1 = "gmir.g_select"(%c, %lshr, %x) : (i1, i32, i32) -> i32
    "test.test"(%r1) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_ashr"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %ashr = "gmir.g_ashr"(%x, %k) : (i32, i32) -> i32
    %r2 = "gmir.g_select"(%c, %ashr, %x) : (i1, i32, i32) -> i32
    "test.test"(%r2) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sub"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %sub = "gmir.g_sub"(%x, %k) : (i32, i32) -> i32
    %r3 = "gmir.g_select"(%c, %sub, %x) : (i1, i32, i32) -> i32
    "test.test"(%r3) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %add = "gmir.g_add"(%x, %k) : (i32, i32) -> i32
    %r4 = "gmir.g_select"(%c, %add, %x) : (i1, i32, i32) -> i32
    "test.test"(%r4) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_or"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %or = "gmir.g_or"(%x, %k) : (i32, i32) -> i32
    %r5 = "gmir.g_select"(%c, %or, %x) : (i1, i32, i32) -> i32
    "test.test"(%r5) : (i32) -> ()

    // CHECK:      "gmir.g_select"(%[[C]], %[[K]], %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_xor"(%[[X]], %{{.*}}) : (i32, i32) -> i32
    %xor = "gmir.g_xor"(%x, %k) : (i32, i32) -> i32
    %r6 = "gmir.g_select"(%c, %xor, %x) : (i1, i32, i32) -> i32
    "test.test"(%r6) : (i32) -> ()

    // Swapped arms: c ? x : (op x, K) -> op x, (c ? 0 : K).
    // CHECK:      %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i32}> : () -> i32
    // CHECK-NEXT: %[[SEL:.*]] = "gmir.g_select"(%[[C]], %[[ZERO]], %[[K]]) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_add"(%[[X]], %[[SEL]]) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r7 = "gmir.g_select"(%c, %x, %add) : (i1, i32, i32) -> i32
    "test.test"(%r7) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32) -> (), sym_name = "chains_into_constants"}> ({
  ^bb0(%c: i1, %x: i32):
    %k = "gmir.g_constant"() <{value = 16 : i32}> : () -> i32
    // The inner select of two constants folds too, leaving no `g_select`.
    // CHECK-LABEL: func.func @chains_into_constants
    // CHECK-NOT:   g_select
    // CHECK:       %[[E:.*]] = "gmir.g_zext"(%{{.*}}) : (i1) -> i32
    // CHECK:       %[[A:.*]] = "gmir.g_shl"(%[[E]], %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT:  %[[R:.*]] = "gmir.g_shl"(%{{.*}}, %[[A]]) : (i32, i32) -> i32
    // CHECK-NEXT:  "test.test"(%[[R]])
    %shl = "gmir.g_shl"(%x, %k) : (i32, i32) -> i32
    %r = "gmir.g_select"(%c, %shl, %x) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i1, i32, i32, i64) -> (), sym_name = "no_folds"}> ({
  ^bb0(%c: i1, %x: i32, %y: i32, %wide: i64):
    %k = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32
    %add = "gmir.g_add"(%x, %k) : (i32, i32) -> i32
    %sub = "gmir.g_sub"(%k, %x) : (i32, i32) -> i32
    %mul = "gmir.g_mul"(%x, %k) : (i32, i32) -> i32
    %var = "gmir.g_add"(%x, %y) : (i32, i32) -> i32

    // CHECK-LABEL: func.func @no_folds
    // The other arm is not the operand of the operation.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r0 = "gmir.g_select"(%c, %add, %y) : (i1, i32, i32) -> i32
    "test.test"(%r0) : (i32) -> ()

    // `K - x` is not `x` when its right operand is `0`.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r1 = "gmir.g_select"(%c, %sub, %x) : (i1, i32, i32) -> i32
    "test.test"(%r1) : (i32) -> ()

    // `0` is not the identity of `g_mul`.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r2 = "gmir.g_select"(%c, %mul, %x) : (i1, i32, i32) -> i32
    "test.test"(%r2) : (i32) -> ()

    // The right operand is not a constant.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    %r3 = "gmir.g_select"(%c, %var, %x) : (i1, i32, i32) -> i32
    "test.test"(%r3) : (i32) -> ()

    // A condition wider than `i1`.
    // CHECK:       "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i32, i32) -> i32
    %r4 = "gmir.g_select"(%wide, %add, %x) : (i64, i32, i32) -> i32
    "test.test"(%r4) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
