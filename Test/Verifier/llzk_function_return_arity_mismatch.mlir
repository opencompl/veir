// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.return: Expected function.return to have 1 operand(s)
"builtin.module"() ({
  "function.def"() <{sym_name = "arity_mismatch", function_type = () -> !felt.type}> ({
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
