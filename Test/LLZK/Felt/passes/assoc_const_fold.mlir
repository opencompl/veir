// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Felt associativity canonicalization:
//   felt.add (felt.add x c1) c2  ->  felt.add x (c1+c2)
// Soundness theorem in Veir/Passes/Felt/Proofs.lean (`assoc_const_fold_add`).
//
// Combined with constant_fold_add, this lets the pass fully fold long
// sums of constants into a single rewrite. Demonstrates a pattern that
// walks the defining op chain (matchAddFromValue + matchConstFromValue)
// without needing dominance reasoning beyond what getDefiningOp! gives.

"builtin.module"() ({
^bb0(%x: !felt.type<"babybear">):
  // ((x + 10) + 32) ->[assoc] (x + 42) ->[const-fold doesn't apply: lhs isn't const]
  // The assoc pattern fires, producing felt.add %x (felt.const 42).
  %c10 = "felt.const"() <{"value" = #felt<const 10> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.add"(%x, %c10) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %c32 = "felt.const"() <{"value" = #felt<const 32> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %outer = "felt.add"(%inner, %c32) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
}) : () -> ()

// After felt-combine: %outer = felt.add %x (felt.const 42).
// The combined const literal value = 42.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 42> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK:          %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK-NEXT:   }) : () -> ()
