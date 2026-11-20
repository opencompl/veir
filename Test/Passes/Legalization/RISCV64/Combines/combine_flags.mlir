// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// The flags of the matched operations do not carry over to new operations whose operands differ.

"builtin.module"() ({
  // In i4, x = y = 0b1000 and z = 1 make `(x << z) | (y << z)` a disjoint `0 | 0`, while `x | y`
  // overlaps. So the hoisted `or` is not disjoint.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "hoist"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %xz = "gmir.g_shl"(%x, %z) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %yz = "gmir.g_shl"(%y, %z) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %or = "gmir.g_or"(%xz, %yz) <{isDisjoint}> : (i64, i64) -> i64
    "func.return"(%or) : (i64) -> ()
  }) : () -> ()

  // In i8, `(127 - 100) - 100` is `-73`, while `127 - -56` overflows.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "constant_reassoc"}> ({
  ^bb0(%a: i8):
    %c = "gmir.g_constant"() <{value = 100 : i8}> : () -> i8
    %s = "gmir.g_sub"(%a, %c) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %r = "gmir.g_sub"(%s, %c) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // `zext nneg (zext x)` holds for any `x`, but `zext nneg x` does not.
  "func.func"() <{function_type = (i16) -> i64, sym_name = "zext_of_zext"}> ({
  ^bb0(%x: i16):
    %mid = "gmir.g_zext"(%x) : (i16) -> i32
    %r = "gmir.g_zext"(%mid) <{nonNeg}> : (i32) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @hoist
// CHECK-SAME:  (%[[X:.*]]: i64, %[[Y:.*]]: i64, %[[Z:.*]]: i64)
// CHECK-NEXT:  %[[OR:.*]] = "gmir.g_or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_shl"(%[[OR]], %[[Z]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R]])

// CHECK-LABEL: func.func @constant_reassoc
// CHECK-SAME:  (%[[A:.*]]: i8)
// CHECK-NEXT:  %[[C:.*]] = "gmir.g_constant"() <{"value" = -56 : i8}>
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_sub"(%[[A]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT:  "func.return"(%[[R]])

// CHECK-LABEL: func.func @zext_of_zext
// CHECK-SAME:  (%[[X:.*]]: i16)
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_zext"(%[[X]]) : (i16) -> i64
// CHECK-NEXT:  "func.return"(%[[R]])
