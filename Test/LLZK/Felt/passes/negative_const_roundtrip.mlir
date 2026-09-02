// RUN: veir-opt %s | filecheck %s
// Negative Felt constants round-trip.

"builtin.module"() ({
  // CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const -42>}> : () -> !felt.type
  %0 = "felt.const"() <{value = #felt<const -42> : !felt.type}> : () -> !felt.type
  // CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0>}> : () -> !felt.type
  %1 = "felt.const"() <{value = #felt<const 0> : !felt.type}> : () -> !felt.type
}) : () -> ()
