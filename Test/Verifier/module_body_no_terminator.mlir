// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name="foo"}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK:        "func.func"() <{
// CHECK-SAME:     "function_type" = () -> ()
// CHECK-SAME:   }> ({
// CHECK:          "func.return"() : () -> ()
