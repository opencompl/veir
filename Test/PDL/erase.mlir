// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operand"() : () -> !pdl.value
    %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.value) -> !pdl.operation
    "pdl.rewrite"(%1) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      "pdl.erase"(%1) : (!pdl.operation) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.value) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "pdl.erase"(%{{.*}}) : (!pdl.operation) -> ()
// CHECK-NEXT:         }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
