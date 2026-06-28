// RUN: not veir-opt %s 2>&1 | filecheck %s

// A graph region captures %x from ^A, but ^A does not dominate ^B (the block
// that owns the graph region), so %x does not dominate its use. The use is in a
// NON-entry block (^g1) of the multi-block graph region, which must still be
// checked.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "m"}> ({
  ^entry(%c : i1):
    "cf.cond_br"(%c) [^A, ^B] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^A():
    %x = "test.test"() : () -> i64
    "cf.br"() [^B] : () -> ()
  ^B():
    "test.test"() ({
    ^g0():
      "test.test"() : () -> ()
    ^g1():
      "test.test"(%x) : (i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: does not dominate its use
