// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

// `(fshl x, z, y) | (shl x, y)` collapses to the funnel shift `fshl x, z, y`: the
// plain shift is subsumed by the funnel shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32, i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32, %z: i32, %y: i32):
    %f = "gmir.g_fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_shl"(%x, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Commuted operand order: shl on the left, fshl on the right.
  "func.func"() <{function_type = (i32, i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32, %z: i32, %y: i32):
    %f = "gmir.g_fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_shl"(%x, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%s, %f) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the shl base differs from the funnel-shift data operand, so the
  // OR stays.
  "func.func"() <{function_type = (i32, i32, i32, i32) -> i32, sym_name = "baz"}> ({
  ^bb0(%x: i32, %z: i32, %y: i32, %w: i32):
    %f = "gmir.g_fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_shl"(%w, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The OR collapses to the fshl (direct order).
// CHECK:      func.func @foo(%[[X:.*]]: i32, %[[Z:.*]]: i32, %[[Y:.*]]: i32) -> i32 {
// CHECK:      %[[F:.*]] = "gmir.g_fshl"(%[[X]], %[[Z]], %[[Y]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "gmir.g_or"
// CHECK:      "func.return"(%[[F]]) : (i32) -> ()

// The OR collapses to the fshl (commuted order).
// CHECK:      func.func @bar(%[[X2:.*]]: i32, %[[Z2:.*]]: i32, %[[Y2:.*]]: i32) -> i32 {
// CHECK:      %[[F2:.*]] = "gmir.g_fshl"(%[[X2]], %[[Z2]], %[[Y2]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "gmir.g_or"
// CHECK:      "func.return"(%[[F2]]) : (i32) -> ()

// Mismatched shl base: the OR survives.
// CHECK:      func.func @baz(%[[NX:.*]]: i32, %[[NZ:.*]]: i32, %[[NY:.*]]: i32, %[[NW:.*]]: i32) -> i32 {
// CHECK:      %[[NR:.*]] = "gmir.g_or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
