// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name="foo"}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK:        func.func @foo() {
// CHECK:          "func.return"() : () -> ()
// CHECK:        }

