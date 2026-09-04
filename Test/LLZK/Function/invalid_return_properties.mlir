// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    // CHECK: function.return: expected no properties, but got 1 property
    "function.return"() <{unexpected = true}> : () -> ()
  }) : () -> ()
}) : () -> ()
