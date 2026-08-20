// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// A block must end in an operation that *might* be a terminator, not one that is
// known to be

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^bb0():
    "test.maybe_terminator"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"()
// CHECK:   "test.maybe_terminator"() : () -> ()
