// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// Telescoping rewrites:
//   (x + c) - c -> x    (add_sub_const_cancel)
//   (x - c) + c -> x    (sub_add_const_cancel)

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  // CHECK:          "function.def"
  "function.def"() <{sym_name = "telescoping", function_type = (!felt.type, !felt.type, !felt.type) -> ()}> ({
// CHECK:          ^{{.*}}:
^bb0(%a: !felt.type, %b: !felt.type, %anchor: !felt.type):
  %c5 = "felt.const"() <{"value" = #felt<const 5> : !felt.type}> : () -> !felt.type
  // (a + 5) - 5 -> a
  %a_plus  = "felt.add"(%a, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t1      = "felt.sub"(%a_plus, %c5) : (!felt.type, !felt.type) -> !felt.type
  // (b - 5) + 5 -> b
  %b_minus = "felt.sub"(%b, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t2      = "felt.add"(%b_minus, %c5) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%t1, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "constrain.eq"({{.*}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%t2, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
