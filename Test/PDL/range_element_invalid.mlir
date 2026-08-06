// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Every argument of a `pdl.range` contributes elements of the result's kind.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
    "pdl.rewrite"(%1) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      %2 = "pdl.range"(%0) : (!pdl.type) -> !pdl.range<value>
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.range: Expected operand 0 to have element type '!pdl.value'
