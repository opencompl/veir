// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>}> ({
  ^bb0():
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.func: Expected symbol name
