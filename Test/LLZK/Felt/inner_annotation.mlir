// RUN: veir-opt %s | filecheck %s
//
// Current, inferred, and legacy forms canonicalize to LLZK's generic form.

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
^bb0():
  // Current syntax.
  // CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 42 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %0 = "felt.const"() <{"value" = #felt<const 42 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  // Legacy `: <"name">` syntax.
  // CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 7 : !felt.type<"bn254">>}> : () -> !felt.type<"bn254">
  %1 = "felt.const"() <{"value" = #felt<const 7 : <"bn254">> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
  // Original legacy body without the colon.
  // CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 99 : !felt.type<"goldilocks">>}> : () -> !felt.type<"goldilocks">
  %2 = "felt.const"() <{"value" = #felt<const 99 <"goldilocks">> : !felt.type<"goldilocks">}> : () -> !felt.type<"goldilocks">
  // Default type inferred from an attribute without an outer annotation.
  // CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 35>}> : () -> !felt.type
  %3 = "felt.const"() <{"value" = #felt<const 35>}> : () -> !felt.type
  // Named type inferred from the v1 field-name annotation.
  // CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 35 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %4 = "felt.const"() <{"value" = #felt<const 35 <"babybear">>}> : () -> !felt.type<"babybear">
// CHECK-NEXT: }) : () -> ()
}) : () -> ()
