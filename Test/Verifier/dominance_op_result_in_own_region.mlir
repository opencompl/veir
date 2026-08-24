// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// An operation dominates the operations nested in its own regions, but its
// *results* do not: they are only available once the operation has run. So
// `%v` may not be used inside the region of the operation that defines it,
// even though that region is a graph region.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    %v = "unreg.wrapper"() ({
      "unreg.use"(%v) : (i64) -> ()
    }) : () -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand #0 does not dominate this use
