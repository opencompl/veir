// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.types"() <{"constantTypes" = [i32, i64]}> : () -> !pdl.range<type>
    %1 = "pdl.operands"(%0) : (!pdl.range<type>) -> !pdl.range<value>
    %2 = "pdl.operation"(%1, %0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.range<value>, !pdl.range<type>) -> !pdl.operation
    %3 = "pdl.results"(%2) : (!pdl.operation) -> !pdl.range<value>
    %4 = "pdl.results"(%2) <{"index" = 0 : i32}> : (!pdl.operation) -> !pdl.value
    "pdl.rewrite"(%2) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      %5 = "pdl.range"(%4, %3) : (!pdl.value, !pdl.range<value>) -> !pdl.range<value>
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "pdl.types"() <{"constantTypes" = [i32, i64]}> : () -> !pdl.range<type>
// CHECK-NEXT:         %{{.*}} = "pdl.operands"(%{{.*}}) : (!pdl.range<type>) -> !pdl.range<value>
// CHECK-NEXT:         %{{.*}} = "pdl.operation"(%{{.*}}, %{{.*}}) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!pdl.range<value>, !pdl.range<type>) -> !pdl.operation
// CHECK-NEXT:         %{{.*}} = "pdl.results"(%{{.*}}) : (!pdl.operation) -> !pdl.range<value>
// CHECK-NEXT:         %{{.*}} = "pdl.results"(%{{.*}}) <{"index" = 0 : i32}> : (!pdl.operation) -> !pdl.value
// CHECK-NEXT:         "pdl.rewrite"(%{{.*}}) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             %{{.*}} = "pdl.range"(%{{.*}}, %{{.*}}) : (!pdl.value, !pdl.range<value>) -> !pdl.range<value>
// CHECK-NEXT:         }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
