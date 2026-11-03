// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  // Replace the matched operation with another operation:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    %1 = "pdl.operand"() : () -> !pdl.value
    %2 = "pdl.operation"(%1, %0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
    "pdl.rewrite"(%2) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      %3 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "bar.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
      "pdl.replace"(%2, %3) <{"operandSegmentSizes" = array<i32: 1, 1, 0>}> : (!pdl.operation, !pdl.operation) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
  // Replace the matched operation with a list of values:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    %1 = "pdl.operand"() : () -> !pdl.value
    %2 = "pdl.operation"(%1, %0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
    "pdl.rewrite"(%2) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      "pdl.replace"(%2, %1) <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.operation, !pdl.value) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}, %{{.*}}) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %{{.*}} = "pdl.operation"(%{{.*}}) <{"attributeValueNames" = [], "opName" = "bar.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
// CHECK-NEXT:             "pdl.replace"(%{{.*}}, %{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 1, 0>}> : (!pdl.operation, !pdl.operation) -> ()
// CHECK-NEXT:         }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}, %{{.*}}) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "pdl.replace"(%{{.*}}, %{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.operation, !pdl.value) -> ()
// CHECK-NEXT:         }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
