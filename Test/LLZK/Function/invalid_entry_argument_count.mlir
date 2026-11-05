// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: Error verifying input program: function.def: entry block must have 1 arguments to match function signature
  "function.def"() <{sym_name = "bad", function_type = (!felt.type) -> ()}> ({
  ^entry:
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
