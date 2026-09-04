// RUN: veir-opt -p=llzk-dedup-constraints %s | filecheck %s
//
// Duplicate `constrain.eq` assertions collapse to one; distinct ones survive.
// Note %2 = a*b + 3 is asserted equal to %a twice, and once against %b.

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "dedup", function_type = (!felt.type, !felt.type) -> ()}> ({
  // CHECK:         ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
  ^bb0(%a: !felt.type, %b: !felt.type):
    // CHECK-NEXT:      %{{.*}} = "felt.mul"
    %0 = "felt.mul"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:      %{{.*}} = "felt.const"
    %1 = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
    // CHECK-NEXT:      %{{.*}} = "felt.add"
    %2 = "felt.add"(%0, %1) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:      "constrain.eq"
    "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
    "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
    // CHECK-NEXT:      "constrain.eq"
    "constrain.eq"(%2, %b) : (!felt.type, !felt.type) -> ()
    "constrain.eq"(%2, %a) : (!felt.type, !felt.type) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
