// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: VEIR_MLIR_SAME_VERDICT

// The entry block of a region may not have predecessors. Here ^bb1 branches back
// to the entry block ^bb0, which would mean the region is re-entered through its
// entry block and breaks the assumption that the entry block dominates the rest
// of the region.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^bb0():
    "cf.br"() [^bb1] : () -> ()
  ^bb1():
    "cf.br"() [^bb0] : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: entry block of a region may not have predecessors
