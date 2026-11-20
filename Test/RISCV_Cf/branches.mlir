// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "foo"}> ({
      ^6(%arg6_0 : !riscv.reg):
        "riscv_cf.branch"(%arg6_0) [^7] : (!riscv.reg) -> ()
      ^7(%arg7_0 : !riscv.reg):
        "riscv_cf.blt"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^8] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^8(%arg8_0 : !riscv.reg):
        "riscv_cf.bge"(%arg8_0, %arg8_0, %arg8_0, %arg8_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^9(%arg9_0 : !riscv.reg):
        "riscv_cf.bltu"(%arg9_0, %arg9_0, %arg9_0, %arg9_0) [^11, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^10(%arg10_0 : !riscv.reg):
        "riscv_cf.bgeu"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^9, ^11] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^11(%arg11_0 : !riscv.reg):
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (!riscv.reg) -> (), "sym_name" = "foo"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.branch"(%{{.*}}) [^[[b_blt:.*]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[b_blt]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.blt"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bltu:.*]], ^[[b_bge:.*]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b_bge]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.bge"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bgeu:.*]], ^[[b_bltu]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b_bltu]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.bltu"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_ret:.*]], ^[[b_bgeu]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b_bgeu]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.bgeu"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b_bltu]], ^[[b_ret]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b_ret]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
