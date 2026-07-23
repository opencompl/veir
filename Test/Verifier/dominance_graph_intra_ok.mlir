// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_VALID

// The uses in ^g1 are never dominance-checked: as in MLIR, dominance is only
// verified in blocks reachable from their region's entry, and ^g1 has no
// predecessors, so it is unreachable (the same rule as in
// dominance_graph_capture.mlir). In particular the program does NOT verify
// because of graph-region block-ordering leniency -- a multi-block region has
// no such leniency: it always has SSA dominance, whatever operation owns it
// (see getDominanceInfo in mlir/lib/IR/Dominance.cpp and
// dominance_multi_block_use_before_def.mlir). The captured %v would be a legal
// use even in a checked block, since it dominates the region-owning operation.
// The program verifies.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "m"}> ({
  ^entry():
    %v = "test.test"() : () -> i64
    "test.test"() ({
    ^g0():
      %a = "test.test"() : () -> i64
    ^g1():
      "test.test"(%a, %v) : (i64, i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "test.test"(%{{.*}}, %{{.*}}) : (i64, i64) -> ()
