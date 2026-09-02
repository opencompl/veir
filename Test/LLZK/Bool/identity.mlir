// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = (i1, i1) -> (), "sym_name" = "bool_identity"}> ({
  "function.def"() <{sym_name = "bool_identity", function_type = (i1, i1) -> ()}> ({
  // CHECK-NEXT:    ^{{.*}}(%{{.*}}: i1, %{{.*}}: i1):
  ^bb0(%a: i1, %b: i1):
    // CHECK-NEXT:      %{{.*}} = "bool.and"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
    %0 = "bool.and"(%a, %b) : (i1, i1) -> i1
    // CHECK-NEXT:      %{{.*}} = "bool.or"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
    %1 = "bool.or"(%a, %b) : (i1, i1) -> i1
    // CHECK-NEXT:      %{{.*}} = "bool.xor"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
    %2 = "bool.xor"(%a, %b) : (i1, i1) -> i1
    // CHECK-NEXT:      %{{.*}} = "bool.not"(%{{.*}}) : (i1) -> i1
    %3 = "bool.not"(%a) : (i1) -> i1
    // CHECK-NEXT:      "bool.assert"(%{{.*}}) : (i1) -> ()
    "bool.assert"(%0) : (i1) -> ()
    // CHECK-NEXT:      "bool.assert"(%{{.*}}) <{"msg" = "expected true"}> : (i1) -> ()
    "bool.assert"(%0) <{msg = "expected true"}> : (i1) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK-NEXT:    }) {function.allow_non_native_field_ops} : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
