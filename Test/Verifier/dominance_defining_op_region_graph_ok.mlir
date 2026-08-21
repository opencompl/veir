// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// The graph-region counterpart of dominance_defining_op_region.mlir. There the
// defining operation sat in an SSACFG region, so it did not dominate the uses
// it encloses. Here it sits directly in the module body, a single-block graph
// region, where every operation of the block dominates every other one whatever
// the source order -- and, as in MLIR, that leniency extends to the operations
// nested in its own regions. So this program verifies (mlir-opt accepts it too).

"builtin.module"() ({
  %x = "test.test"() ({
    "test.test"(%x) : (i32) -> ()
  }) : () -> i32
}) : () -> ()

// CHECK:      %[[X:.*]] = "test.test"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "test.test"(%[[X]]) : (i32) -> ()
