// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The replacement is either an operation or a list of values, never both.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operand"() : () -> !pdl.value
    %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.value) -> !pdl.operation
    "pdl.rewrite"(%1) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      %2 = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "bar.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
      "pdl.replace"(%1, %2, %0) <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (!pdl.operation, !pdl.operation, !pdl.value) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.replace: Expected no replacement values when the replacement operation is present
