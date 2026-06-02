// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "func.func"() ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK:        "func.func"() ({
// CHECK:          "func.return"() : () -> ()
