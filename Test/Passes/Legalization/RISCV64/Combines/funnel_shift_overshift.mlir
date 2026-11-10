// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

// A funnel shift amount is taken modulo the bit-width, so an over-large constant
// amount is reduced to its residue: `fshl/fshr x, y, C -> fshl/fshr x, y, C % bw`
// when `C >= bw`.

"builtin.module"() ({
  // fshl by 35 on i32 reduces the amount to 35 % 32 = 3.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_constant"() <{value = 35 : i32}> : () -> i32
    %r = "gmir.g_fshl"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // fshr by 40 on i32 reduces the amount to 40 % 32 = 8.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_constant"() <{value = 40 : i32}> : () -> i32
    %r = "gmir.g_fshr"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // fshl by -1 on i32 reads the amount as unsigned and reduces it to 31.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "unsigned"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_constant"() <{value = -1 : i32}> : () -> i32
    %r = "gmir.g_fshl"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // The amount may be wider than the shifted values. It is still taken modulo
  // their width: 35 % 32 = 3, even though 35 fits in the i64 amount.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "wide_amount"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_constant"() <{value = 35 : i64}> : () -> i64
    %r = "gmir.g_fshl"(%x, %y, %c) : (i32, i32, i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the amount is already less than the width, so it stays.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "baz"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32
    %r = "gmir.g_fshl"(%x, %y, %c) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// fshl amount reduced to 3.
// CHECK:      func.func @foo(%[[X:.*]]: i32, %[[Y:.*]]: i32) -> i32 {
// CHECK:      %[[A:.*]] = "gmir.g_constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "gmir.g_fshl"(%[[X]], %[[Y]], %[[A]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// fshr amount reduced to 8.
// CHECK:      func.func @bar(%[[X2:.*]]: i32, %[[Y2:.*]]: i32) -> i32 {
// CHECK:      %[[A2:.*]] = "gmir.g_constant"() <{"value" = 8 : i32}> : () -> i32
// CHECK:      %[[R2:.*]] = "gmir.g_fshr"(%[[X2]], %[[Y2]], %[[A2]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[R2]]) : (i32) -> ()

// fshl amount reduced to 31.
// CHECK:      func.func @unsigned(%[[X3:.*]]: i32, %[[Y3:.*]]: i32) -> i32 {
// CHECK:      %[[A3:.*]] = "gmir.g_constant"() <{"value" = 31 : i32}> : () -> i32
// CHECK:      %[[R3:.*]] = "gmir.g_fshl"(%[[X3]], %[[Y3]], %[[A3]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[R3]]) : (i32) -> ()

// Wide amount reduced to 3, and still an i64.
// CHECK:      func.func @wide_amount(%[[X4:.*]]: i32, %[[Y4:.*]]: i32) -> i32 {
// CHECK:      %[[A4:.*]] = "gmir.g_constant"() <{"value" = 3 : i64}> : () -> i64
// CHECK:      %[[R4:.*]] = "gmir.g_fshl"(%[[X4]], %[[Y4]], %[[A4]]) : (i32, i32, i64) -> i32
// CHECK:      "func.return"(%[[R4]]) : (i32) -> ()

// In-range amount: the funnel shift is unchanged.
// CHECK:      func.func @baz(%[[NX:.*]]: i32, %[[NY:.*]]: i32) -> i32 {
// CHECK:      %[[NC:.*]] = "gmir.g_constant"() <{"value" = 5 : i32}> : () -> i32
// CHECK:      %[[NR:.*]] = "gmir.g_fshl"(%[[NX]], %[[NY]], %[[NC]]) : (i32, i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
