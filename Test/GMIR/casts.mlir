// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%a: i8, %b: i64):
  %anyext = "gmir.g_anyext"(%a) : (i8) -> i64
  %sext = "gmir.g_sext"(%a) : (i8) -> i64
  %zext = "gmir.g_zext"(%a) : (i8) -> i64
  %trunc = "gmir.g_trunc"(%b) : (i64) -> i8
}) : () -> ()

// CHECK: "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
// CHECK: "gmir.g_sext"(%{{.*}}) : (i8) -> i64
// CHECK: "gmir.g_zext"(%{{.*}}) : (i8) -> i64
// CHECK: "gmir.g_trunc"(%{{.*}}) : (i64) -> i8
