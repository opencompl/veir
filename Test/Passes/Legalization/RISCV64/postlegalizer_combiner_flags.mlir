// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
    %x = "test.test"() : () -> i64
    %c = "gmir.g_constant"() <{value = 5 : i64}> : () -> i64
    %min = "gmir.g_constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    // `sub_to_add` drops `nuw`, and keeps `nsw` unless the constant is the minimum signed value.
    // CHECK:      "gmir.g_add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}>
    %sub = "gmir.g_sub"(%x, %c) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // CHECK:      "gmir.g_add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    %sub_min = "gmir.g_sub"(%x, %min) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // `sub_to_addw` reads the low 32 bits of the constant: it sign-extends their negation, and
    // drops `nsw` when they are the minimum signed `i32` value, even when the `i64` constant is not.
    %w_min = "gmir.g_constant"() <{value = -2147483648 : i64}> : () -> i64
    %w_min_zext = "gmir.g_constant"() <{value = 2147483648 : i64}> : () -> i64
    // CHECK:      %[[NEG5:.*]] = "gmir.g_constant"() <{"value" = -5 : i64}>
    // CHECK-NEXT: "gmir.g_addw"(%{{.*}}, %[[NEG5]]) <{"overflowFlags" = 1 : i32}>
    %subw = "gmir.g_subw"(%x, %c) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // CHECK:      %[[MIN:.*]] = "gmir.g_constant"() <{"value" = -2147483648 : i64}>
    // CHECK-NEXT: "gmir.g_addw"(%{{.*}}, %[[MIN]]) : (i64, i64) -> i64
    %subw_min = "gmir.g_subw"(%x, %w_min) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // CHECK:      %[[MIN2:.*]] = "gmir.g_constant"() <{"value" = -2147483648 : i64}>
    // CHECK-NEXT: "gmir.g_addw"(%{{.*}}, %[[MIN2]]) : (i64, i64) -> i64
    %subw_min_zext = "gmir.g_subw"(%x, %w_min_zext) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "test.test"(%sub, %sub_min, %subw, %subw_min, %subw_min_zext) : (i64, i64, i64, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
