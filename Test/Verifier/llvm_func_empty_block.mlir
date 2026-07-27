// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
  ^bb0():
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.func: Expected the block to end in a terminator, but the block is empty
