// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i32):
        "riscv_cf.branch"(%arg6_0) [^7] : (i32) -> ()
      ^7(%arg7_0 : i32):
        "riscv_cf.beq"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^10(%arg10_0 : i32):
        "riscv_cf.bne"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
      ^9(%arg9_0 : i32):
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "func.func"() ({
// CHECK-NEXT:       ^6(%arg6_0 : i32):
// CHECK-NEXT:         "riscv_cf.branch"(%arg6_0) [^7] : (i32) -> ()
// CHECK-NEXT:       ^7(%arg7_0 : i32):
// CHECK-NEXT:         "riscv_cf.beq"(%arg7_0, %arg7_0, %arg7_0, %arg7_0) [^9, ^10] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^10(%arg10_0 : i32):
// CHECK-NEXT:         "riscv_cf.bne"(%arg10_0, %arg10_0, %arg10_0, %arg10_0) [^10, ^9] <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1>}> : (i32, i32, i32, i32) -> ()
// CHECK-NEXT:       ^9(%arg9_0 : i32):
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
