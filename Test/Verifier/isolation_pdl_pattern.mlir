// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// pdl.pattern is isolated from above, so its body may not capture a PDL handle
// defined in the module body.

"builtin.module"() ({
  %t = "pdl.type"() : () -> !pdl.type
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %root = "pdl.operation"(%t) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
    "pdl.rewrite"(%root) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      "pdl.erase"(%root) : (!pdl.operation) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.operation: operand uses a value defined outside the isolated region
