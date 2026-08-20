// RUN: veir-opt %s --allow-unregistered-dialect | filecheck %s
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// A block must end in an operation that *might* be a terminator, not one that is
// known to be. This mirrors MLIR, which gates the check on
// `mightHaveTrait<OpTrait::IsTerminator>` (`verifyOnExit(Block &)` in
// mlir/lib/IR/Verifier.cpp), and `mightHaveTrait` is `!isRegistered() ||
// hasTrait(...)`: an unregistered operation might carry any trait, so it is
// accepted in terminator position. Here the func.func body ends in an
// unregistered op, which mlir-opt accepts and VeIR must too.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^bb0():
    "test.maybe_terminator"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"()
// CHECK:   "test.maybe_terminator"() : () -> ()
