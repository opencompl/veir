// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: Error verifying input program: function.def: entry block expected 1 argument(s), got 0
  "function.def"() <{sym_name = "bad", function_type = (!felt.type) -> ()}> ({
  ^entry:
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
