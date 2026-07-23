// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> ()}> ({
  ^bb0():
    "func.return"() : () -> ()
    %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: Expected a terminator to be the last operation of its block
