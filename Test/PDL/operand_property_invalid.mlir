// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.operand` carries no properties.
"builtin.module"() ({
  %0 = "pdl.operand"() <{"constantType" = i32}> : () -> !pdl.value
}) : () -> ()

// CHECK: pdl.operand: expected no properties, but got 1 property
