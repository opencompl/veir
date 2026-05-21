// RUN: veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^0(%arg0 : i32):
      "func.return"(%arg0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error: No entry point: define a function named 'main' or use top-level executable ops
