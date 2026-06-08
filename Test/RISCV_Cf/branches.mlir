// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^6(%arg6_0 : i32):
        "riscv_cf.branch"(%arg6_0) [^7] : (i32) -> ()
      ^7(%arg7_0 : i32):
        "riscv_cf.blt"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^8] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^8(%arg8_0 : i32):
        "riscv_cf.bge"(%arg8_0, %arg8_0, %arg8_0, %arg8_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^9(%arg9_0 : i32):
        "riscv_cf.bltu"(%arg9_0, %arg9_0, %arg9_0, %arg9_0) [^11, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^10(%arg10_0 : i32):
        "riscv_cf.bgeu"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^9, ^11] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^11(%arg11_0 : i32):
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (i32) -> ()}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.branch"(%{{.*}}) [^[[b_blt:.*]]] : (i32) -> ()
// CHECK-NEXT:       ^[[b_blt]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.blt"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bltu:.*]], ^[[b_bge:.*]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b_bge]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.bge"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bgeu:.*]], ^[[b_bltu]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b_bltu]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.bltu"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_ret:.*]], ^[[b_bgeu]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b_bgeu]](%{{.*}} : i32):
// CHECK-NEXT:         "riscv_cf.bgeu"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bltu]], ^[[b_ret]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^[[b_ret]](%{{.*}} : i32):
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
