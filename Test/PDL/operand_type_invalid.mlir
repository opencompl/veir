// RUN: not veir-opt %s 2>&1 | filecheck %s

// The `valueType` operand of a `pdl.attribute` is a `!pdl.type` handle, not the
// type the attribute is constrained to.
"builtin.module"() ({
  %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
  %1 = "pdl.attribute"(%0) : (i32) -> !pdl.attribute
}) : () -> ()

// CHECK: pdl.attribute: Expected the `valueType` operand to be of type '!pdl.type'
