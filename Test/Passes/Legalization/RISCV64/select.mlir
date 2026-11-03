// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i8, i8) -> (), sym_name = "main"}> ({
  ^bb0(%c: i1, %t: i8, %f: i8):
    // The values are any-extended and the result is truncated back. The condition is
    // zero-extended, since a nonzero condition is true.
    // CHECK:      %[[T:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: %[[F:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i1) -> i64
    // CHECK-NEXT: %[[ONE:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[COND:.*]] = "gmir.g_and"(%[[EXT]], %[[ONE]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[SEL:.*]] = "gmir.g_select"(%[[COND]], %[[T]], %[[F]]) : (i64, i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[SEL]]) : (i64) -> i8
    %r = "gmir.g_select"(%c, %t, %f) : (i1, i8, i8) -> i8
    "test.test"(%r) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
