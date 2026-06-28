// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_AGREE

// A non-isolated nested region (the body of an unregistered test.test op) may
// reference values from an enclosing region. Only IsolatedFromAbove ops, such as
// func.func, form a barrier, so this program verifies.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "f"}> ({
  ^bb0(%a : i64):
    "test.test"() ({
    ^bb1():
      "test.test"(%a) : (i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[A:.*]] : i64):
// CHECK:        "test.test"(%[[A]]) : (i64) -> ()
