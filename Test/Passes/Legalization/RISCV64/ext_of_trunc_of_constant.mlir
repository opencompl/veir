// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// `g_sext (g_trunc c)` and `g_zext (g_trunc c)` of a `g_constant` `c` fold to `c` when the
// truncation keeps its signed (unsigned) value, as LLVM's `tryCombineSExt` and `tryCombineZExt`
// do with known bits.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (i64, i64, i64, i64, i64), sym_name = "fold"}> ({
    %c63 = "gmir.g_constant"() <{value = 63 : i64}> : () -> i64
    %cm1 = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %cmin = "gmir.g_constant"() <{value = -2147483648 : i64}> : () -> i64
    %cmax = "gmir.g_constant"() <{value = 4294967295 : i64}> : () -> i64
    %t63 = "gmir.g_trunc"(%c63) : (i64) -> i32
    %tm1 = "gmir.g_trunc"(%cm1) : (i64) -> i32
    %tmin = "gmir.g_trunc"(%cmin) : (i64) -> i32
    %tmax = "gmir.g_trunc"(%cmax) : (i64) -> i32
    %s63 = "gmir.g_sext"(%t63) : (i32) -> i64
    %sm1 = "gmir.g_sext"(%tm1) : (i32) -> i64
    %smin = "gmir.g_sext"(%tmin) : (i32) -> i64
    %z63 = "gmir.g_zext"(%t63) : (i32) -> i64
    %zmax = "gmir.g_zext"(%tmax) : (i32) -> i64
    "func.return"(%s63, %sm1, %smin, %z63, %zmax) : (i64, i64, i64, i64, i64) -> ()
  }) : () -> ()

  // Negative cases: the truncation changes the value.
  "func.func"() <{function_type = () -> (i64, i64), sym_name = "keep"}> ({
    %big = "gmir.g_constant"() <{value = 2147483648 : i64}> : () -> i64
    %neg = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %tbig = "gmir.g_trunc"(%big) : (i64) -> i32
    %tneg = "gmir.g_trunc"(%neg) : (i64) -> i32
    %sbig = "gmir.g_sext"(%tbig) : (i32) -> i64
    %zneg = "gmir.g_zext"(%tneg) : (i32) -> i64
    "func.return"(%sbig, %zneg) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @fold
// CHECK:       %[[C63:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
// CHECK:       %[[CM1:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}>
// CHECK:       %[[CMIN:.*]] = "gmir.g_constant"() <{"value" = -2147483648 : i64}>
// CHECK:       %[[CMAX:.*]] = "gmir.g_constant"() <{"value" = 4294967295 : i64}>
// CHECK-NOT:   "gmir.g_sext"
// CHECK-NOT:   "gmir.g_zext"
// CHECK:       "func.return"(%[[C63]], %[[CM1]], %[[CMIN]], %[[C63]], %[[CMAX]])

// CHECK-LABEL: func.func @keep
// CHECK:       %[[SBIG:.*]] = "gmir.g_sext"
// CHECK:       %[[ZNEG:.*]] = "gmir.g_zext"
// CHECK:       "func.return"(%[[SBIG]], %[[ZNEG]])
