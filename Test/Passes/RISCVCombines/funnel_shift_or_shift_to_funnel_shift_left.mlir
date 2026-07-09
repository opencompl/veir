// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(fshl x, z, y) | (shl x, y)` collapses to the funnel shift `fshl x, z, y`: the
// plain shift is subsumed by the funnel shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32, i32) -> i32}> ({
  ^bb0(%x: i32, %z: i32, %y: i32):
    %f = "llvm.intr.fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "llvm.shl"(%x, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Commuted operand order: shl on the left, fshl on the right.
  "func.func"() <{function_type = (i32, i32, i32) -> i32}> ({
  ^bb0(%x: i32, %z: i32, %y: i32):
    %f = "llvm.intr.fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "llvm.shl"(%x, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%s, %f) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the shl base differs from the funnel-shift data operand, so the
  // OR stays.
  "func.func"() <{function_type = (i32, i32, i32, i32) -> i32}> ({
  ^bb0(%x: i32, %z: i32, %y: i32, %w: i32):
    %f = "llvm.intr.fshl"(%x, %z, %y) : (i32, i32, i32) -> i32
    %s = "llvm.shl"(%w, %y) : (i32, i32) -> i32
    %r = "llvm.or"(%f, %s) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The OR collapses to the fshl (direct order).
// CHECK:      ^{{.*}}(%[[X:.*]] : i32, %[[Z:.*]] : i32, %[[Y:.*]] : i32):
// CHECK:      %[[F:.*]] = "llvm.intr.fshl"(%[[X]], %[[Z]], %[[Y]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "llvm.or"
// CHECK:      "func.return"(%[[F]]) : (i32) -> ()

// The OR collapses to the fshl (commuted order).
// CHECK:      ^{{.*}}(%[[X2:.*]] : i32, %[[Z2:.*]] : i32, %[[Y2:.*]] : i32):
// CHECK:      %[[F2:.*]] = "llvm.intr.fshl"(%[[X2]], %[[Z2]], %[[Y2]]) : (i32, i32, i32) -> i32
// CHECK-NOT:  "llvm.or"
// CHECK:      "func.return"(%[[F2]]) : (i32) -> ()

// Mismatched shl base: the OR survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32, %[[NZ:.*]] : i32, %[[NY:.*]] : i32, %[[NW:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
