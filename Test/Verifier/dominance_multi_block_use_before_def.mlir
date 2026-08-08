// RUN: not veir-opt %s 2>&1 | filecheck %s

// A multi-block region always has SSA dominance, no matter what operation owns
// it: as in MLIR (see getDominanceInfo in mlir/lib/IR/Dominance.cpp), graph
// region leniency is only granted to single-block regions. Adding a second
// block to the region of dominance_graph_single_block_ok.mlir therefore makes
// the use-before-def in the (always reachable) entry block a dominance error.
// mlir-opt rejects this program the same way ("operand #0 does not dominate
// this use"); we cannot assert that with MLIR_INVALID because mlir-opt already
// rejects the unregistered test ops without --allow-unregistered-dialect.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "m"}> ({
  ^entry():
    "test.test"() ({
    ^g0():
      "test.test"(%a) : (i64) -> ()
      %a = "test.test"() : () -> i64
    ^g1():
      "test.test"() : () -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: does not dominate its use
