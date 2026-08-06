// RUN: veir-opt %s -p=canonicalize | filecheck %s

// The rewrite actions in a pattern body produce no results, so treating them as
// side-effect free would let dead-code elimination delete them. `mlir-opt
// -canonicalize` leaves this pattern untouched.
"builtin.module"() ({
  "pdl.pattern"() <{benefit = 1 : i16}> ({
    %0 = "pdl.operation"() <{attributeValueNames = [], opName = "foo.bar", operandSegmentSizes = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{operandSegmentSizes = array<i32: 1, 0>}> ({
      "pdl.erase"(%0) : (!pdl.operation) -> ()
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "pdl.pattern"() <{"benefit" = 1 : i16}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[root:.*]] = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.bar", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:         "pdl.rewrite"(%[[root]]) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
// CHECK-NEXT:           ^{{.*}}():
// CHECK-NEXT:             "pdl.erase"(%[[root]]) : (!pdl.operation) -> ()
// CHECK-NEXT:         }) : (!pdl.operation) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
