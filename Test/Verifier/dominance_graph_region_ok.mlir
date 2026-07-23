// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_VALID

// A multi-block region always has SSA dominance, even under an unregistered op
// (as in MLIR; see getDominanceInfo in mlir/lib/IR/Dominance.cpp), so ^bb0 does
// not get to feed ^bb1 by graph-region leniency. The program still verifies
// because dominance is only checked in blocks reachable from their region's
// entry, and ^bb1 has no predecessors: the use of %v is never checked.

"builtin.module"() ({
  "test.test"() ({
  ^bb0:
    %v = "test.test"() : () -> i32
  ^bb1:
    "test.test"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[V:.*]] = "test.test"() : () -> i32
// CHECK:      "test.test"(%[[V]]) : (i32) -> ()
