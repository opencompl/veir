// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// The synthesized zero preserves the operand's named field type.

"builtin.module"() ({
  "function.def"() <{sym_name = "self_subtraction_named_field", function_type = (!felt.type<"bn254">, !felt.type<"bn254">) -> ()}> ({
^bb0(%x: !felt.type<"bn254">, %anchor: !felt.type<"bn254">):
  // CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0 : !felt.type<"bn254">>}> : () -> !felt.type<"bn254">
  %s = "felt.sub"(%x, %x) : (!felt.type<"bn254">, !felt.type<"bn254">) -> !felt.type<"bn254">
  "constrain.eq"(%s, %anchor) : (!felt.type<"bn254">, !felt.type<"bn254">) -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
