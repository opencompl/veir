// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "f"}> ({
  ^bb0(%arg0: i32):
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected 1 func.return operand(s)
