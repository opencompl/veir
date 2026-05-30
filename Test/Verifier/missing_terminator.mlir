// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
  ^bb0():
    %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
  }) : () -> ()
}) : () -> ()

// CHECK: Expected the last operation of a block to be a terminator
