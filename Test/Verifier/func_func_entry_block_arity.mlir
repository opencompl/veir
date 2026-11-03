// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: not veir-interpret %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `main` takes no arguments, but its entry block has one.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
  ^bb0(%a: i32):
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.func: entry block must have 0 arguments to match function signature
