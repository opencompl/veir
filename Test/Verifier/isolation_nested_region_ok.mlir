// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_ROUNDTRIP

// A non-isolated nested region may capture a value from its enclosing
// function region.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "f"}> ({
  ^entry(%arg : i64):
    "test.test"() ({
      "test.test"(%arg) : (i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[ARG:.*]] : i64):
// CHECK:        "test.test"(%[[ARG]]) : (i64) -> ()
