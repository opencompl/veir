// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.attribute` is constrained either by an expected type or by a constant
// value, but never by both. The `valueType` operand will be a `!pdl.type`
// handle once `pdl.type` is modelled.
"builtin.module"() ({
  %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
  %1 = "pdl.attribute"(%0) <{"value" = "hello"}> : (i32) -> !pdl.attribute
}) : () -> ()

// CHECK: pdl.attribute: Expected only one of [`type`, `value`] to be set
