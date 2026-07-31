// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.attribute` is constrained either by an expected type or by a constant
// value, but never by both. `test.test` stands in for `pdl.type`, which is not
// modelled yet.
"builtin.module"() ({
  %0 = "test.test"() : () -> !pdl.type
  %1 = "pdl.attribute"(%0) <{"value" = "hello"}> : (!pdl.type) -> !pdl.attribute
}) : () -> ()

// CHECK: pdl.attribute: Expected only one of [`type`, `value`] to be set
