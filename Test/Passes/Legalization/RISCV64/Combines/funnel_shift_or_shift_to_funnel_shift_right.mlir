// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

// `(fshr z, x, y) | (lshr x, y)` collapses to the funnel shift `fshr z, x, y`: the
// plain shift is subsumed by the funnel shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32, i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%z: i32, %x: i32, %y: i32):
    %f = "gmir.g_fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_lshr"(%x, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Commuted operand order: lshr on the left, fshr on the right.
  "func.func"() <{function_type = (i32, i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%z: i32, %x: i32, %y: i32):
    %f = "gmir.g_fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_lshr"(%x, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%s, %f) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the lshr base differs from the funnel-shift data operand, so the
  // OR stays.
  "func.func"() <{function_type = (i32, i32, i32, i32) -> i32, sym_name = "baz"}> ({
  ^bb0(%z: i32, %x: i32, %y: i32, %w: i32):
    %f = "gmir.g_fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "gmir.g_lshr"(%w, %y) : (i32, i32) -> i32
    %r = "gmir.g_or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The OR collapses to the fshr (direct order).
// CHECK:      func.func @foo(%[[Z:.*]]: i32, %[[X:.*]]: i32, %[[Y:.*]]: i32) -> i32 {
// CHECK:      %[[F:.*]] = "gmir.g_fshr"(%[[Z]], %[[X]], %[[Y]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "gmir.g_or"
// CHECK:      "func.return"(%[[F]]) : (i32) -> ()

// The OR collapses to the fshr (commuted order).
// CHECK:      func.func @bar(%[[Z2:.*]]: i32, %[[X2:.*]]: i32, %[[Y2:.*]]: i32) -> i32 {
// CHECK:      %[[F2:.*]] = "gmir.g_fshr"(%[[Z2]], %[[X2]], %[[Y2]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "gmir.g_or"
// CHECK:      "func.return"(%[[F2]]) : (i32) -> ()

// Mismatched lshr base: the OR survives.
// CHECK:      func.func @baz(%[[NZ:.*]]: i32, %[[NX:.*]]: i32, %[[NY:.*]]: i32, %[[NW:.*]]: i32) -> i32 {
// CHECK:      %[[NR:.*]] = "gmir.g_or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
