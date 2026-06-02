// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
  ^bb0():
    "func.return"() : () -> ()
    %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected a terminator to be the last operation of its block
