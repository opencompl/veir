// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    // Define an external operand:
    %0 = "pdl.operand"() : () -> !pdl.value
    // Define an external operand with an expected type:
    %1 = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
    %2 = "pdl.operand"(%1) : (!pdl.type) -> !pdl.value
    %3 = "pdl.operation"(%0, %2) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 0, 0>}> : (!pdl.value, !pdl.value) -> !pdl.operation
    "pdl.rewrite"(%3) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
// CHECK-NEXT:         %{{.*}} = "pdl.operand"(%{{.*}}) : (!pdl.type) -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}, %{{.*}}) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 0, 0>}> : (!pdl.value, !pdl.value) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({        }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
