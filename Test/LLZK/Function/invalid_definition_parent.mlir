// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "outer", function_type = () -> ()}> ({
    // CHECK: function.def: expected parent to be builtin.module
    "function.def"() <{sym_name = "inner", function_type = () -> ()}> ({
      "function.return"() : () -> ()
    }) : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
