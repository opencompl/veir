// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The `valueType` operand of a `pdl.operands` is a `!pdl.range<type>` handle.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    %1 = "pdl.operands"(%0) : (!pdl.type) -> !pdl.range<value>
    %2 = "pdl.operation"(%1) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.range<value>) -> !pdl.operation
    "pdl.rewrite"(%2) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.operands: Expected the `valueType` operand to be of type '!pdl.range<type>'
