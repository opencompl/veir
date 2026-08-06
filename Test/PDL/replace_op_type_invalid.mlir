// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The replaced `opValue` is an `!pdl.operation` handle.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operand"() : () -> !pdl.value
    %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.value) -> !pdl.operation
    "pdl.rewrite"(%1) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      "pdl.replace"(%0, %0) <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.value) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.replace: Expected the `opValue` operand to be of type '!pdl.operation'
