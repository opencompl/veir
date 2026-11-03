// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.def: 'function.arg_name' is only valid on function arguments
"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> (), function.arg_name = "x"}> ({
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
