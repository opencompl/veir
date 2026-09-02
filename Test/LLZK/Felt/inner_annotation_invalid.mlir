// RUN: not veir-opt %s 2>&1 | filecheck %s
// Legacy inner and outer field names must agree.
// CHECK: inner field name disagrees with outer
"builtin.module"() ({
  %0 = "felt.const"() <{"value" = #felt<const 1 : <"babybear">> : !felt.type<"bn254">}> : () -> !felt.type<"bn254">
}) : () -> ()
