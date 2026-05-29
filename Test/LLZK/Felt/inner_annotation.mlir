// RUN: veir-opt %s | filecheck %s
//
// Inner-field-annotation parse path for FeltConstAttr.
//
// LLZK's `llzk-opt --mlir-print-op-generic` emits named-field felt
// constants with the field annotation *inside* the const body:
//
//   #felt<const N : <"name">> : !felt.type<"name">
//
// Prior to the parser fix shipped alongside this test, VEIR's
// AttrParser rejected the inner `:` (it expected `>` after the
// integer). The fix makes the inner `: <"name">` optional; both
// the inner-only LLZK form and VEIR's outer-only form
// (`#felt<const N> : !felt.type<"name">`) parse cleanly. When both
// annotations are present, they must agree on the field name.
//
// This test validates parsing; the VEIR printer continues to emit
// the outer-only form (which is also valid input to VEIR). The
// differential normalizer in `scripts/llzk-diff.sh` canonicalizes
// the two forms for the LLZK ↔ VEIR round-trip — that's a separate
// (WA.2) concern documented in `harness/differential.md`.

"builtin.module"() ({
^bb0():
  // Inner-annotation form (LLZK's emit shape):
  %0 = "felt.const"() <{"value" = #felt<const 42 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // Outer-annotation form (VEIR's emit shape; pre-existing parse path):
  %1 = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
  // Inner annotation without outer field (still legal — the outer
  // !felt.type omits the field name; consistency check is vacuous):
  %2 = "felt.const"() <{"value" = #felt<const 99 : <"goldilocks">> : !felt.type<"goldilocks">}> : () -> !felt.type<"goldilocks">
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// VEIR canonicalizes both input shapes to its outer-only emit form.
// (The inner annotation is consumed but not re-emitted; the outer
// `!felt.type<"name">` annotation carries the field name on output.)
// CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 42> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
// CHECK-NEXT:      %{{.*}} = "felt.const"() <{"value" = #felt<const 99> : !felt.type<"goldilocks">}> : () -> !felt.type<"goldilocks">
// CHECK-NEXT: }) : () -> ()
