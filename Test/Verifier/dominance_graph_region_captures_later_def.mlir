// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// A graph region relaxes the ordering between points *inside* the region. It
// says nothing about values the region captures from an enclosing SSACFG
// region: those must still be defined before the operation that encloses the
// use. `%v` is defined after `unreg.wrapper`, so it does not dominate the use
// nested inside it.
//
// The region of an unregistered operation is a graph region, so this also pins
// down that dominance is checked inside graph regions rather than skipped.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
  ^entry:
    "unreg.wrapper"() ({
      "unreg.use"(%v) : (i64) -> ()
    }) : () -> ()
    %v = "unreg.def"() : () -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand #0 does not dominate this use
