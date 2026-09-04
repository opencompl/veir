// RUN: veir-opt %s | filecheck %s
//
// bool.cmp with all six FeltCmpPredicate values.

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "bool_cmp", function_type = (!felt.type, !felt.type) -> ()}> ({
// CHECK:         ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
^bb0(%a: !felt.type, %b: !felt.type):
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp eq>}> : (!felt.type, !felt.type) -> i1
  %eq = "bool.cmp"(%a, %b) <{predicate = #bool<cmp eq>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp ne>}> : (!felt.type, !felt.type) -> i1
  %ne = "bool.cmp"(%a, %b) <{predicate = #bool<cmp ne>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp lt>}> : (!felt.type, !felt.type) -> i1
  %lt = "bool.cmp"(%a, %b) <{predicate = #bool<cmp lt>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp le>}> : (!felt.type, !felt.type) -> i1
  %le = "bool.cmp"(%a, %b) <{predicate = #bool<cmp le>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp gt>}> : (!felt.type, !felt.type) -> i1
  %gt = "bool.cmp"(%a, %b) <{predicate = #bool<cmp gt>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp ge>}> : (!felt.type, !felt.type) -> i1
  %ge = "bool.cmp"(%a, %b) <{predicate = #bool<cmp ge>}> : (!felt.type, !felt.type) -> i1
  // CHECK-NEXT:      "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
