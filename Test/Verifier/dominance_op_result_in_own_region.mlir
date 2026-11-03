// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// An operation dominates the operations nested in its own regions, but its
// *results* do not: they are only available once the operation has run. So
// `%v` may not be used inside the region of the operation that defines it,
// even though every region of a `test` operation is a graph region.
//
// `mlir-opt` does not know the operation, hence MLIR_UNREGISTERED_INVALID; it
// rejects the input for the same reason, as its own dominance query excludes
// the enclosing operation when the value is one of its results.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    %v = "test.test"() ({
      "test.test"(%v) : (i64) -> ()
    }) : () -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: test.test: operand #0 does not dominate this use
