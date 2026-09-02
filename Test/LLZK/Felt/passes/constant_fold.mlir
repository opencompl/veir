// RUN: veir-opt %s -p="canonicalize" | filecheck %s
// Fold two constants while preserving mixed constant/value additions.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "constant_fold", function_type = (!felt.type<"babybear">, !felt.type<"babybear">) -> ()}> ({
^bb0(%v: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  // Both operands constant: folds to felt.const 42.
  // CHECK-NOT:    #felt<const 10>
  %a = "felt.const"() <{"value" = #felt<const 10 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:    #felt<const 32>
  %b = "felt.const"() <{"value" = #felt<const 32 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 42 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %sum = "felt.add"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // Mixed: a constant + a block-arg value. Constant-fold does NOT match;
  // right-identity pattern also doesn't (rhs is 5, not 0). Op survives.
  // CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 5 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %five = "felt.const"() <{"value" = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK:          %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %mixed = "felt.add"(%v, %five) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%sum, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%mixed, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
// CHECK:        }) : () -> ()
}) : () -> ()
