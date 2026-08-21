// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// An operation's results are not available inside that operation's own
// regions. Although the nested use is textually after the result name, the
// defining operation does not properly dominate operations that it encloses.
// This is the `enclosingOk := false` case of `InsertPoint.dominates`; the
// defining operation lives in the SSACFG region of `func.func`. See
// dominance_defining_op_region_graph_ok.mlir for the graph-region counterpart,
// where the same shape is accepted.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    %x = "test.test"() ({
      "test.test"(%x) : (i32) -> ()
    }) : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand 0 {{.*}} does not dominate its use
