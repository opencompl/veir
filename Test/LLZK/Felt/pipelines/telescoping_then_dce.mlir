// RUN: veir-opt %s -p="felt-combine,dce" | filecheck %s
// Telescoping reduces `(a + 5) - 5` to `a`; DCE removes the dead operations.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "telescoping_then_dce", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %b: !felt.type):
  // CHECK-NOT:    "felt.const"
  %c5      = "felt.const"() <{value = #felt<const 5> : !felt.type}> : () -> !felt.type
  // CHECK-NOT:    "felt.add"
  %a_plus  = "felt.add"(%a, %c5) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NOT:    "felt.sub"
  %t1      = "felt.sub"(%a_plus, %c5) : (!felt.type, !felt.type) -> !felt.type
  // CHECK:          "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%t1, %b) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
