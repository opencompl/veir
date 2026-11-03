// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.def: 'arg_attrs' expected 1 entries, got 0
"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = (i1) -> (), arg_attrs = []}> ({
  ^entry(%x : i1):
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
