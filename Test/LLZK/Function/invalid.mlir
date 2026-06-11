// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: function.def with 2 regions instead of 1 triggers
// the typed verifier arm. Confirms the .function .«def» path is
// reached (the unregistered fallthrough accepts any arity).

// CHECK: Error verifying input program: Expected 1 region
"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    "function.return"() : () -> ()
  }, {
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
