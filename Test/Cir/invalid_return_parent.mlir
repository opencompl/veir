// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Expected cir.return to be enclosed by cir.func
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "f"}> ({
    "cir.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
