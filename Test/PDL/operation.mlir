// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  // Define an operation with no constraints:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
  // Define an operation with a name:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
  // Define an operation with operands, attributes and result types:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operand"() : () -> !pdl.value
    %1 = "pdl.operand"() : () -> !pdl.value
    %2 = "pdl.attribute"() : () -> !pdl.attribute
    %3 = "pdl.type"() : () -> !pdl.type
    %4 = "pdl.operation"(%0, %1, %2, %3) <{"attributeValueNames" = ["attrA"], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 1, 1>}> : (!pdl.value, !pdl.value, !pdl.attribute, !pdl.type) -> !pdl.operation
    "pdl.rewrite"(%4) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({        }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({        }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.attribute"() : () -> !pdl.attribute
// CHECK-NEXT:         %{{.*}} = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"attributeValueNames" = ["attrA"], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 1, 1>}> : (!pdl.value, !pdl.value, !pdl.attribute, !pdl.type) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({        }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
