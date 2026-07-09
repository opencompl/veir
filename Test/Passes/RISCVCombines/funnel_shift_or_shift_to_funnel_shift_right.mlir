// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(fshr z, x, y) | (lshr x, y)` collapses to the funnel shift `fshr z, x, y`: the
// plain shift is subsumed by the funnel shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32, i32) -> i32}> ({
  ^bb0(%z: i32, %x: i32, %y: i32):
    %f = "llvm.intr.fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "llvm.lshr"(%x, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Commuted operand order: lshr on the left, fshr on the right.
  "func.func"() <{function_type = (i32, i32, i32) -> i32}> ({
  ^bb0(%z: i32, %x: i32, %y: i32):
    %f = "llvm.intr.fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "llvm.lshr"(%x, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%s, %f) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the lshr base differs from the funnel-shift data operand, so the
  // OR stays.
  "func.func"() <{function_type = (i32, i32, i32, i32) -> i32}> ({
  ^bb0(%z: i32, %x: i32, %y: i32, %w: i32):
    %f = "llvm.intr.fshr"(%z, %x, %y) : (i32, i32, i32) -> i32
    %s = "llvm.lshr"(%w, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The OR collapses to the fshr (direct order).
// CHECK:      ^{{.*}}(%[[Z:.*]] : i32, %[[X:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[F:.*]] = "llvm.intr.fshr"(%[[Z]], %[[X]], %[[Y]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "llvm.or"
// CHECK:      "func.return"(%[[F]]) : (i32) -> ()

// The OR collapses to the fshr (commuted order).
// CHECK:      ^{{.*}}(%[[Z2:.*]] : i32, %[[X2:.*]] : i32, %[[Y2:.*]] : i32):
// CHECK:      %[[F2:.*]] = "llvm.intr.fshr"(%[[Z2]], %[[X2]], %[[Y2]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "llvm.or"
// CHECK:      "func.return"(%[[F2]]) : (i32) -> ()

// Mismatched lshr base: the OR survives.
// CHECK:      ^{{.*}}(%[[NZ:.*]] : i32, %[[NX:.*]] : i32, %[[NY:.*]] : i32, %[[NW:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
