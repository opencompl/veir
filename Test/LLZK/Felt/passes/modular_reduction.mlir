// RUN: veir-opt %s -p="canonicalize" | filecheck %s
// Registered-field folds reduce modulo the field modulus.
// Bare felt types do not fold because their modulus is unresolved.

// CHECK:          "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "modular_reduction", function_type = (!felt.type<"babybear">, !felt.type) -> ()}> ({
^bb0(%anchor: !felt.type<"babybear">, %raw_anchor: !felt.type):
  %add_a = "felt.const"() <{"value" = #felt<const 2013265920 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %add_b = "felt.const"() <{"value" = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:        #felt<const 2013265922 : !felt.type<"babybear">>
  // CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 1 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %add = "felt.add"(%add_a, %add_b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">

  %neg_in = "felt.const"() <{"value" = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:        #felt<const -5 : !felt.type<"babybear">>
  // CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265916 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %neg = "felt.neg"(%neg_in) : (!felt.type<"babybear">) -> !felt.type<"babybear">

  // CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265920>}> : () -> !felt.type
  %raw_a = "felt.const"() <{"value" = #felt<const 2013265920> : !felt.type}> : () -> !felt.type
  // CHECK-DAG:        %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2>}> : () -> !felt.type
  %raw_b = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
  // CHECK-NOT:        #felt<const 2013265922>
  // CHECK:            %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
  %raw_add = "felt.add"(%raw_a, %raw_b) : (!felt.type, !felt.type) -> !felt.type

  "constrain.eq"(%add, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%neg, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%raw_add, %raw_anchor) : (!felt.type, !felt.type) -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
// CHECK:          }) : () -> ()
}) : () -> ()
