// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The entry block is its own predecessor, which the rule rejects just the same:
// a single-block region cannot loop back to its own entry.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^bb0:
    "cf.br"() [^bb0] : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: entry block of region may not have predecessors
