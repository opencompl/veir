// RUN: not veir-opt %s 2>&1 | filecheck %s

// The `valueType` operand of a `pdl.operand` is a `!pdl.type` handle, not the
// type the operand is constrained to.
"builtin.module"() ({
  %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
  %1 = "pdl.operand"(%0) : (i32) -> !pdl.value
}) : () -> ()

// CHECK: pdl.operand: Expected the `valueType` operand to be of type '!pdl.type'
