// RUN: not veir-interpret %s 2>&1 | filecheck %s

// Check that a block given fewer values than it has arguments cannot be interpreted: `main` takes
// no arguments, but its entry block has one.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
  ^bb0(%a: i32):
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: failed to interpret module
