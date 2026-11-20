// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64, i64) -> (i64, i64, i64, i64), sym_name = "fold"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64, %z: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %three = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %i0 = "gmir.g_icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i64
    %i1 = "gmir.g_icmp"(%y, %z) <{predicate = 1 : i64}> : (i64, i64) -> i64
    %s0 = "gmir.g_select"(%c, %i0, %zero) : (i64, i64, i64) -> i64
    %s1 = "gmir.g_select"(%c, %one, %i1) : (i64, i64, i64) -> i64
    %s2 = "gmir.g_select"(%c, %i0, %i1) : (i64, i64, i64) -> i64
    %s3 = "gmir.g_select"(%c, %one, %zero) : (i64, i64, i64) -> i64
    %a0 = "gmir.g_and"(%s0, %one) : (i64, i64) -> i64
    %a1 = "gmir.g_and"(%s1, %one) : (i64, i64) -> i64
    %a2 = "gmir.g_and"(%s2, %three) : (i64, i64) -> i64
    %a3 = "gmir.g_and"(%s3, %one) : (i64, i64) -> i64
    "func.return"(%a0, %a1, %a2, %a3) : (i64, i64, i64, i64) -> ()
  }) : () -> ()

  // Negative cases: an arm may be other than 0 or 1, or the mask clears the low bit.
  "func.func"() <{function_type = (i64, i64, i64) -> (i64, i64), sym_name = "keep"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %two = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %i0 = "gmir.g_icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i64
    %s0 = "gmir.g_select"(%c, %x, %zero) : (i64, i64, i64) -> i64
    %s1 = "gmir.g_select"(%c, %i0, %zero) : (i64, i64, i64) -> i64
    %a0 = "gmir.g_and"(%s0, %one) : (i64, i64) -> i64
    %a1 = "gmir.g_and"(%s1, %two) : (i64, i64) -> i64
    "func.return"(%a0, %a1) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @fold
// CHECK:       %[[S0:.*]] = "gmir.g_select"
// CHECK:       %[[S1:.*]] = "gmir.g_select"
// CHECK:       %[[S2:.*]] = "gmir.g_select"
// CHECK:       %[[S3:.*]] = "gmir.g_select"
// CHECK-NOT:   "gmir.g_and"
// CHECK:       "func.return"(%[[S0]], %[[S1]], %[[S2]], %[[S3]])

// CHECK-LABEL: func.func @keep
// CHECK:       %[[A0:.*]] = "gmir.g_and"
// CHECK:       %[[A1:.*]] = "gmir.g_and"
// CHECK:       "func.return"(%[[A0]], %[[A1]])
