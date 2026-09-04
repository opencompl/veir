// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = () -> ()}> ({
    // CHECK: Error verifying input program: include.from: Expected the parent operation to be a builtin.module
    "include.from"() <{sym_name = "nested", path = "nested.llzk"}> : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
