// RUN: veir-opt %s -p="canonicalize,felt-combine" | filecheck %s
// Canonicalization moves zero to the right before felt-combine removes the add.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  // CHECK:          "function.def"
  "function.def"() <{sym_name = "add_const_canonicalize", function_type = (!felt.type, !felt.type) -> ()}> ({
// CHECK:          ^{{.*}}:
^bb0(%a: !felt.type, %anchor: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  // Constant on the LEFT. Without canonicalization,
  // right_identity_zero_add (which matches `add x const`) wouldn't fire.
  %r = "felt.add"(%z, %a) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
