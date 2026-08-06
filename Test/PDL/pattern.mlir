// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  // A named pattern whose rewrite is given inline by the body region:
  "pdl.pattern"() <{"benefit" = 2 : i16, "sym_name" = "named"}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    %1 = "pdl.operand"() : () -> !pdl.value
    %2 = "pdl.operation"(%1, %0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
    "pdl.rewrite"(%2) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      %3 = "pdl.operation"(%0) <{"attributeValueNames" = [], "opName" = "bar.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
    }) : (!pdl.operation) -> ()
  }) : () -> ()
  // An anonymous pattern delegating to an external rewrite function:
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "baz.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 2 : i16, "sym_name" = "named"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[t:.*]] = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:         %[[v:.*]] = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:         %[[root:.*]] = "pdl.operation"(%[[v]], %[[t]]) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.value, !pdl.type) -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%[[root]]) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %{{.*}} = "pdl.operation"(%[[t]]) <{"attributeValueNames" = [], "opName" = "bar.op", "operandSegmentSizes" = array<i32: 0, 0, 1>}> : (!pdl.type) -> !pdl.operation
// CHECK-NEXT:     }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[op:.*]] = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "baz.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%[[op]]) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({{.*}}) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
