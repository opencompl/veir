// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_ROUNDTRIP

// IsolatedFromAbove only rejects definitions outside the function. The use in
// ^dead refers to a definition in a nested region of the same function, so it
// satisfies isolation. MLIR also accepts the program because ordinary
// dominance is not checked in unreachable blocks.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "f"}> ({
  ^entry():
    "func.return"() : () -> ()
  ^dead():
    "test.test"(%v) : (i32) -> ()
    "test.test"() ({
      %v = "arith.constant"() <{value = 0 : i32}> : () -> i32
      "test.test"(%v) : (i32) -> ()
    }) : () -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "test.test"(%[[V:.*]]) : (i32) -> ()
// CHECK:      %[[V]] = "arith.constant"()
