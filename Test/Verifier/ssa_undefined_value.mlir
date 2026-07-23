// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Every used SSA name must be defined somewhere. A use of a name that is never
// assigned is rejected by the parser, before verification runs.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "main"}> ({
  ^bb0():
    "func.return"(%missing) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: use of undefined value %missing
