// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> ()}> ({
  ^bb0():
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected symbol name
