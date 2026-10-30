// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `c ? C1 : C2` for a 0-or-1 `g_icmp` `c` becomes `(c << k) + C2` when `C1 - C2 = 2^k`, and
// `C2 - (c << k)` when `C2 - C1 = 2^k`. A shift by 0 folds away.

"builtin.module"() ({
  // C1 - C2 = 8.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "add"}> ({
  ^bb0(%a: i64, %b: i64):
    %c = "gmir.g_icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    %c1 = "gmir.g_constant"() <{value = 108 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 100 : i64}> : () -> i64
    %r = "gmir.g_select"(%c, %c1, %c2) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // C2 - C1 = 1: the `? 2 : 1` of libdivide, at 32 bits.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "sub"}> ({
  ^bb0(%a: i64, %b: i64):
    %c = "gmir.g_icmp"(%a, %b) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    %c1 = "gmir.g_constant"() <{value = 4294967294 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 4294967295 : i64}> : () -> i64
    %r = "gmir.g_select"(%c, %c1, %c2) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @add
// CHECK:       %[[C:.*]] = "gmir.g_icmp"
// CHECK:       %[[SH:.*]] = "gmir.g_shl"(%[[C]], %{{.*}})
// CHECK:       "gmir.g_add"(%[[SH]], %{{.*}})
// CHECK-NOT:   "gmir.g_select"

// CHECK-LABEL: func.func @sub
// CHECK:       %[[C2:.*]] = "gmir.g_icmp"
// CHECK:       "gmir.g_sub"(%{{.*}}, %[[C2]])
// CHECK-NOT:   "gmir.g_select"
