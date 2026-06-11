// RUN: not veir-opt %s 2>&1 | filecheck %s
//
// Negative test for the FeltConstAttr inner/outer field-name
// disagreement case. When both annotations are present, they must
// name the same field. The parser surfaces the disagreement as a
// clear diagnostic.

// CHECK: inner field name disagrees with outer
"builtin.module"() ({
  %0 = "felt.const"() <{"value" = #felt<const 1 : <"babybear">> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
}) : () -> ()
