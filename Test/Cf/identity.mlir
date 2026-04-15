// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i32):
        "cf.br"(%arg6_0) [^7] : (i32) -> ()
      ^7(%arg7_0 : i32):
        %9 = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
        "cf.cond_br"(%9, %arg7_0, %arg7_0) [^7, ^7] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "func.func"() ({
// CHECK-NEXT:       ^6(%arg6_0 : i32):
// CHECK-NEXT:         "cf.br"(%arg6_0) [^7] : (i32) -> ()
// CHECK-NEXT:       ^7(%arg7_0 : i32):
// CHECK-NEXT:         %9 = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
// CHECK-NEXT:         "cf.cond_br"(%9, %arg7_0, %arg7_0) [^7, ^7] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
