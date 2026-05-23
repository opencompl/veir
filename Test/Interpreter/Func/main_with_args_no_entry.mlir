// RUN: not veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^0(%arg0 : i32):
      "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error: No entry point: define a zero-argument func.func or llvm.func named 'main'
