// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// A graph region relaxes the ordering between points inside the
// region, but we still need to check whether values captured from
// outside are dominating.

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
