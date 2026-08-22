// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// A graph region imposes no ordering between definitions and uses, so a use may
// precede its definition there. An unregistered operation's regions are graph
// regions (see `Builtin.hasSSADominance`), so the body of `test.wrapper` is one.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "test.wrapper"() ({
      "test.use"(%a) : (i32) -> ()
      %a = "test.def"() : () -> i32
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "test.use"(%[[A:.*]]) : (i32) -> ()
// CHECK-NEXT: %[[A]] = "test.def"() : () -> i32
