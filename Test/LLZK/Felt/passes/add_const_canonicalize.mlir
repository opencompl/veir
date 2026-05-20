// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.add (felt.const c) x  ->  felt.add x (felt.const c)  (canonicalize)
// Followed by right_identity_zero_add firing.
// Soundness: add_const_swap, then right_identity_zero_add.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  // Constant on the LEFT. Without canonicalization,
  // right_identity_zero_add (which matches `add x const`) wouldn't fire.
  %r = "felt.add"(%z, %a) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// After canonicalization the add becomes (a, z); then
// right_identity_zero_add removes it. Final state: only the const op.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NOT:      "felt.add"
// CHECK:        }) : () -> ()
