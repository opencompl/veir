// RUN: not veir-interpret --ctree %s 2>&1 | filecheck %s

// A function without a body cannot be interpreted.
"builtin.module"() ({
  "func.func"() <{sym_name = "ext", function_type = () -> i32, sym_visibility = "private"}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %r = "func.call"() <{callee = @ext}> : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: failed to interpret module
