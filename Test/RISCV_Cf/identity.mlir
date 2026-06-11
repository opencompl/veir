// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^6(%arg6_0 : i32):
        "riscv_cf.branch"(%arg6_0) [^7] : (i32) -> ()
      ^7(%arg7_0 : i32):
        "riscv_cf.beq"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^10(%arg10_0 : i32):
        "riscv_cf.bne"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^9(%arg9_0 : i32):
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (i32) -> ()}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.branch"(%{{.*}}) [^[[b1:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[b1]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.beq"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b3:.*]], ^[[b2:.*]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b2]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.bne"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b2]], ^[[b3]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b3]](%{{.*}} : i32):
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
