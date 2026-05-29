// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() ({
  ^bb0():
  }) : () -> ()
}) : () -> ()

// CHECK: the block is empty
