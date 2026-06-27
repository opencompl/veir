// RUN: veir-opt %s | filecheck %s

// Dominance is only required in SSACFG regions. The body of an unregistered op
// is a graph region, where a value defined in one block may be used in another
// block that it does not dominate, so this program verifies.

"builtin.module"() ({
  "test.test"() ({
  ^bb0:
    %v = "test.test"() : () -> i32
  ^bb1:
    "test.test"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[V:.*]] = "test.test"() : () -> i32
// CHECK:      "test.test"(%[[V]]) : (i32) -> ()
