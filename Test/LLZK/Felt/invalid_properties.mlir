// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: felt: expected no properties, but got 1 property
"builtin.module"() ({
  %0 = "felt.const"() <{value = #felt<const 1 : !felt.type>}> : () -> !felt.type
  %1 = "felt.add"(%0, %0) <{unexpected = true}> : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()
