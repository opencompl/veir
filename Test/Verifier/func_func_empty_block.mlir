// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
  ^bb0():
  }) : () -> ()
}) : () -> ()

// CHECK: func.func: Expected the block to end in a terminator, but the block is empty
