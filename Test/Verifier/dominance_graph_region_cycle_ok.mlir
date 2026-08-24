// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// In a graph region every point properly dominates every other, including
// itself, so a value may be used by its own defining operation and two
// operations may use each other's results. The body of `builtin.module` is a
// graph region.

"builtin.module"() ({
  %a = "arith.addi"(%a, %b) : (i32, i32) -> i32
  %b = "arith.subi"(%a, %a) : (i32, i32) -> i32
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %[[A:.*]] = "arith.addi"(%[[A]], %[[B:.*]]) : (i32, i32) -> i32
// CHECK-NEXT:     %[[B]] = "arith.subi"(%[[A]], %[[A]]) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
