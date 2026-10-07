// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// A non-legal (narrower than `i64`) `gmir.g_add` is widened to a legal `i64` `g_add` with
// `g_anyext` operands and a `g_trunc` result; a legal `i64` `g_add` is left alone.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32, i64, i64) -> (), sym_name = "foo"}> ({
  ^bb0(%a: i32, %b: i32, %c: i64, %d: i64):
    %0 = "gmir.g_add"(%a, %b) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // CHECK:      %[[A:.*]] = "gmir.g_anyext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[B:.*]] = "gmir.g_anyext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[ADD:.*]] = "gmir.g_add"(%[[A]], %[[B]]) : (i64, i64) -> i64
    // CHECK-NEXT: %{{.*}} = "gmir.g_trunc"(%[[ADD]]) : (i64) -> i32
    %1 = "gmir.g_add"(%c, %d) : (i64, i64) -> i64
    // CHECK-NEXT: %{{.*}} = "gmir.g_add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    // CHECK-NOT:  "gmir.g_anyext"
    "test.test"(%0, %1) : (i32, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
