// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// As `dominance_graph_region_captures_later_def.mlir`, but the graph region
// belongs to a registered operation that declares `RegionKind::Graph` rather
// than to an unregistered one. The result is the same: a graph region does not
// excuse a capture from the enclosing SSACFG region that is not yet defined.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    "test.test"() ({
      "test.test"(%v) : (i64) -> ()
    }) : () -> ()
    %v = "test.test"() : () -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand #0 does not dominate this use
