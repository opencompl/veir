// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// A graph region relaxes the ordering between points *inside* the region. It
// says nothing about values the region captures from an enclosing SSACFG
// region: those must still be defined before the operation that encloses the
// use. `%v` is defined after the `test.test` wrapper, so it does not dominate
// the use nested inside it.
//
// Every region of a `test` operation is a graph region, so this also pins down
// that dominance is checked inside graph regions rather than skipped.
// `mlir-opt` does not know the operation, hence MLIR_UNREGISTERED_INVALID;
// there it is an unregistered operation, whose regions are graph regions too,
// so it rejects the input for the same reason.

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
