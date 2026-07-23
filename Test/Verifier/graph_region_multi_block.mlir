// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// builtin.module has a graph region, so its region may have at most one block.
// Graph-region dominance leniency therefore only ever applies to single-block
// regions, as in MLIR.

"builtin.module"() ({
^bb0:
  "func.func"() <{function_type = () -> (), sym_name = "a"}> ({ ^e0: "func.return"() : () -> () }) : () -> ()
^bb1:
  "func.func"() <{function_type = () -> (), sym_name = "b"}> ({ ^e1: "func.return"() : () -> () }) : () -> ()
}) : () -> ()

// CHECK: Graph regions may contain at most one block
