// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `mul x, 2` becomes `shl x, 1`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %c2 = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %r = "gmir.g_mul"(%x, %c2) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: multiplying by 3 does not fold to a shift.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %c3 = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %r = "gmir.g_mul"(%x, %c3) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// mul-by-2 rewritten to x << 1.
// CHECK:      func.func @foo(%[[X:.*]]: i64) -> i64 {
// CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK:      %[[R:.*]] = "gmir.g_shl"(%[[X]], %[[K]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// mul-by-3 is left as a mul.
// CHECK:      func.func @bar(%[[NX:.*]]: i64) -> i64 {
// CHECK:      %[[NR:.*]] = "gmir.g_mul"(%[[NX]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
