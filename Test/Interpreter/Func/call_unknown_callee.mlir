// RUN: not veir-interpret %s 2>&1 | filecheck %s

// A call to a symbol that the module does not define cannot be interpreted.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %r = "func.call"() <{callee = @missing}> : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: call_unknown_callee.mlir:7:5: error: failed to interpret operation
