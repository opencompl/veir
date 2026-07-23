// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: Expected enclosing func.func to have a function_type attribute
