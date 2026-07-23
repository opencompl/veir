// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "f"}> ({
  ^bb0(%arg0: i32):
    "llvm.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.return: Expected llvm.return to be enclosed by llvm.func
