// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = (index, !felt.type) -> (), "sym_name" = "ram_identity"}> ({
  "function.def"() <{sym_name = "ram_identity", function_type = (index, !felt.type) -> ()}> ({
  // CHECK-NEXT:    ^{{.*}}(%{{.*}}: index, %{{.*}}: !felt.type):
  ^bb0(%addr: index, %val: !felt.type):
    // CHECK-NEXT:      "ram.store"(%{{.*}}, %{{.*}}) : (index, !felt.type) -> ()
    "ram.store"(%addr, %val) : (index, !felt.type) -> ()
    // CHECK-NEXT:      %{{.*}} = "ram.load"(%{{.*}}) : (index) -> !felt.type
    %0 = "ram.load"(%addr) : (index) -> !felt.type
    // CHECK-NEXT:      "ram.store"(%{{.*}}, %{{.*}}) : (index, !felt.type) -> ()
    "ram.store"(%addr, %0) : (index, !felt.type) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK-NEXT:    }) {function.allow_witness} : () -> ()
  }) {function.allow_witness} : () -> ()
}) : () -> ()
