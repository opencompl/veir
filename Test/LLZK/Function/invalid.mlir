// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: function.def: Expected 1 region (the function body)
"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    "function.return"() : () -> ()
  }, {
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
