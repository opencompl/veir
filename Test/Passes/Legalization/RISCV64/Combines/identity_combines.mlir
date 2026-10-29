// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// LLVM's identity_combines, and `-1 - x` → `x ^ -1`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (i64, i64, i64, i64, i64, i64, i64), sym_name = "right_identity_zero"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %sub = "gmir.g_sub"(%x, %zero) : (i64, i64) -> i64
    %add = "gmir.g_add"(%x, %zero) : (i64, i64) -> i64
    %or = "gmir.g_or"(%x, %zero) : (i64, i64) -> i64
    %xor = "gmir.g_xor"(%x, %zero) : (i64, i64) -> i64
    %shl = "gmir.g_shl"(%x, %zero) : (i64, i64) -> i64
    %ashr = "gmir.g_ashr"(%x, %zero) : (i64, i64) -> i64
    %lshr = "gmir.g_lshr"(%x, %zero) : (i64, i64) -> i64
    "func.return"(%sub, %add, %or, %xor, %shl, %ashr, %lshr) : (i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64) -> (i64, i64, i64), sym_name = "same_val"}> ({
  ^bb0(%x: i64):
    %and = "gmir.g_and"(%x, %x) : (i64, i64) -> i64
    %or = "gmir.g_or"(%x, %x) : (i64, i64) -> i64
    %sub = "gmir.g_sub"(%x, %x) : (i64, i64) -> i64
    "func.return"(%and, %or, %sub) : (i64, i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64) -> (i64, i64), sym_name = "mul_identities"}> ({
  ^bb0(%x: i64):
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %mulOne = "gmir.g_mul"(%x, %one) : (i64, i64) -> i64
    %mulZero = "gmir.g_mul"(%x, %zero) : (i64, i64) -> i64
    "func.return"(%mulOne, %mulZero) : (i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64) -> i64, sym_name = "sub_minus_one"}> ({
  ^bb0(%x: i64):
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %r = "gmir.g_sub"(%ones, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// `x op 0` is `x` for sub, add, or, xor and the shifts.
// CHECK-LABEL: func.func @right_identity_zero
// CHECK-SAME:  (%[[X:.*]]: i64)
// CHECK-NEXT:  "func.return"(%[[X]], %[[X]], %[[X]], %[[X]], %[[X]], %[[X]], %[[X]])

// `x & x` and `x | x` are `x`; `x - x` is `0`.
// CHECK-LABEL: func.func @same_val
// CHECK-SAME:  (%[[X:.*]]: i64)
// CHECK-NEXT:  %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
// CHECK-NEXT:  "func.return"(%[[X]], %[[X]], %[[Z]])

// `x * 1` is `x`; `x * 0` is `0`.
// CHECK-LABEL: func.func @mul_identities
// CHECK-SAME:  (%[[X:.*]]: i64)
// CHECK-NEXT:  %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
// CHECK-NEXT:  "func.return"(%[[X]], %[[Z]])

// `-1 - x` is `x ^ -1`.
// CHECK-LABEL: func.func @sub_minus_one
// CHECK-SAME:  (%[[X:.*]]: i64)
// CHECK-NEXT:  %[[ONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}>
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_xor"(%[[X]], %[[ONES]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R]])
