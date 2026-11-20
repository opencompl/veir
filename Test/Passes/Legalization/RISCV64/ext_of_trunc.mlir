// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// As in LLVM's artifact combiner, `g_sext (g_trunc x)` is a `g_sext_inreg` of `x`, and
// `g_zext (g_trunc x)` is a `g_and` of `x` with the mask of the truncated width.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (i64, i64), sym_name = "ext_of_trunc"}> ({
  ^bb0(%x : i64):
    // CHECK-LABEL: func.func @ext_of_trunc
    // CHECK-NEXT:  %[[S:.*]] = "gmir.g_sext_inreg"(%[[X:.*]]) <{"sz" = 32 : i64}> : (i64) -> i64
    // CHECK-NEXT:  %[[MASK:.*]] = "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK-NEXT:  %[[Z:.*]] = "gmir.g_and"(%[[X]], %[[MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT:  "func.return"(%[[S]], %[[Z]])
    %t32 = "gmir.g_trunc"(%x) : (i64) -> i32
    %s = "gmir.g_sext"(%t32) : (i32) -> i64
    %t8 = "gmir.g_trunc"(%x) : (i64) -> i8
    %z = "gmir.g_zext"(%t8) : (i8) -> i64
    "func.return"(%s, %z) : (i64, i64) -> ()
  }) : () -> ()

  // A wider `x` is truncated to the type of the extension first, which widening folds again.
  "func.func"() <{function_type = (i64) -> (i32, i32), sym_name = "wider"}> ({
  ^bb0(%x : i64):
    // CHECK-LABEL: func.func @wider
    // CHECK:       %[[S:.*]] = "gmir.g_sext_inreg"(%[[X:.*]]) <{"sz" = 16 : i64}> : (i64) -> i64
    // CHECK-NEXT:  %[[TS:.*]] = "gmir.g_trunc"(%[[S]]) : (i64) -> i32
    // CHECK-NEXT:  %[[MASK:.*]] = "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK-NEXT:  %[[Z:.*]] = "gmir.g_and"(%[[X]], %[[MASK]]) : (i64, i64) -> i64
    // CHECK-NEXT:  %[[TZ:.*]] = "gmir.g_trunc"(%[[Z]]) : (i64) -> i32
    // CHECK-NEXT:  "func.return"(%[[TS]], %[[TZ]])
    %t16 = "gmir.g_trunc"(%x) : (i64) -> i16
    %s = "gmir.g_sext"(%t16) : (i16) -> i32
    %t8 = "gmir.g_trunc"(%x) : (i64) -> i8
    %z = "gmir.g_zext"(%t8) : (i8) -> i32
    "func.return"(%s, %z) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()
