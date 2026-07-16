// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_VALID

// A graph region captures %x from ^A, and ^A does not dominate ^B (the block
// that owns the graph region). The capture is used in a NON-entry block (^g1)
// of the multi-block graph region. Like MLIR, dominance is only checked in
// blocks reachable from their region's entry; ^g1 has no intra-region control
// flow into it, so it is unreachable and the use is not checked. The program
// therefore verifies. (A capture used in the graph region's entry block ^g0 is
// still checked -- see dominance_graph_capture_result.mlir.)

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "m"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c) [^A, ^B] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^A():
    %x = "test.test"() : () -> i64
    "cf.br"() [^B] : () -> ()
  ^B():
    "test.test"() ({
    ^g0():
      "test.test"() : () -> ()
    ^g1():
      "test.test"(%x) : (i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "test.test"(%{{.*}}) : (i64) -> ()
