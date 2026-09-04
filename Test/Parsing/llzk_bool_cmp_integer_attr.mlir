// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "bool_cmp", function_type = (!felt.type, !felt.type) -> ()}> ({
  ^bb0(%a: !felt.type, %b: !felt.type):
    // CHECK: "predicate" = #bool<cmp eq>
    %eq = "bool.cmp"(%a, %b) <{predicate = 0 : i32}> : (!felt.type, !felt.type) -> i1
    "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
