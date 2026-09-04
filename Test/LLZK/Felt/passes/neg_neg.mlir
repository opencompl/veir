// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.neg (felt.neg x) -> x.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  // CHECK:          "function.def"
  "function.def"() <{sym_name = "neg_neg", function_type = (!felt.type, !felt.type) -> ()}> ({
// CHECK:          ^{{.*}}:
^bb0(%a: !felt.type, %anchor: !felt.type):
  %n1 = "felt.neg"(%a) : (!felt.type) -> !felt.type
  %n2 = "felt.neg"(%n1) : (!felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%n2, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
