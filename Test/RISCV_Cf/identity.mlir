// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"()  <{function_type = (!riscv.reg) -> (), sym_name = "foo"}> ({
      ^6(%arg6_0 : !riscv.reg):
        "riscv_cf.branch"(%arg6_0) [^7] : (!riscv.reg) -> ()
      ^7(%arg7_0 : !riscv.reg):
        "riscv_cf.beq"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^10(%arg10_0 : !riscv.reg):
        "riscv_cf.bne"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
      ^9(%arg9_0 : !riscv.reg):
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (!riscv.reg) -> (), "sym_name" = "foo"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.branch"(%{{.*}}) [^[[b1:.*]]] : (!riscv.reg) -> ()
// CHECK-NEXT:       ^[[b1]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.beq"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b3:.*]], ^[[b2:.*]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b2]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "riscv_cf.bne"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) [^[[b2]], ^[[b3]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:       ^[[b3]](%{{.*}} : !riscv.reg):
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
