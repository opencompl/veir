// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_AGREE

// Inside a multi-block graph region there is no block ordering, so %a (defined in
// ^g0) may be used in the sibling block ^g1. The captured value %v dominates the
// graph-owning operation, so it is also a legal use. The program verifies.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "m"}> ({
  ^entry():
    %v = "test.test"() : () -> i64
    "test.test"() ({
    ^g0():
      %a = "test.test"() : () -> i64
    ^g1():
      "test.test"(%a, %v) : (i64, i64) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "test.test"(%{{.*}}, %{{.*}}) : (i64, i64) -> ()
