// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "invalid_constrain", function_type = (!felt.type<"babybear">, !felt.type<"bn254">) -> ()}> ({
  ^bb0(%a: !felt.type<"babybear">, %b: !felt.type<"bn254">):
    // CHECK: Error verifying input program: constrain.eq: expected operands to have the same type
    "constrain.eq"(%a, %b) : (!felt.type<"babybear">, !felt.type<"bn254">) -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
