// RUN: veir-opt %s | filecheck %s
//
// Regression test for the post-2026-05-17 audit's Real Issue #2:
// parseOptionalFeltConstAttr originally passed `allowNegative := false`
// to parseOptionalInteger, breaking the parse∘print round-trip on
// negative values (the printer emits them with a `-`, but the parser
// rejected them with "expected an integer value").

"builtin.module"() ({
  // CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const -42>}> : () -> !felt.type
  %0 = "felt.const"() <{value = #felt<const -42> : !felt.type}> : () -> !felt.type
  // CHECK: %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0>}> : () -> !felt.type
  %1 = "felt.const"() <{value = #felt<const 0> : !felt.type}> : () -> !felt.type
}) : () -> ()
