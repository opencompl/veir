// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `redundant_and` drops an odd mask from a 0-or-1 logic operation of `g_icmp`s, as legalizing a
// `g_brcond` on `a > 0 && b > 0` leaves behind.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %ca = "gmir.g_icmp"(%a, %zero) <{"predicate" = 4 : i64}> : (i64, i64) -> i64
    %cb = "gmir.g_icmp"(%b, %zero) <{"predicate" = 4 : i64}> : (i64, i64) -> i64
    %both = "gmir.g_and"(%ca, %cb) : (i64, i64) -> i64
    %r = "gmir.g_and"(%both, %one) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[CA:.*]] = "gmir.g_icmp"
// CHECK:      %[[CB:.*]] = "gmir.g_icmp"
// CHECK-NEXT: %[[BOTH:.*]] = "gmir.g_and"(%[[CA]], %[[CB]])
// CHECK-NEXT: "func.return"(%[[BOTH]])
