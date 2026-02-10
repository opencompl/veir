// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %arg0 = "riscv.li"() : () -> i64
  %arg1 = "riscv.li"() : () -> i64
    %0 = "riscv.remu"(%arg0, %arg1) : (i64, i64) -> i64
    %1 = "riscv.rem"(%arg0, %0) : (i64, i64) -> i64
    %2 = "riscv.slt"(%arg1, %1) : (i64, i64) -> i64
    %3 = "riscv.xori"(%2) : (i64) -> i64
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %5 = "riscv.li"() : () -> i64
// CHECK-NEXT:     %6 = "riscv.li"() : () -> i64
// CHECK-NEXT:     %7 = "riscv.remu"(%5, %6) : (i64, i64) -> i64
// CHECK-NEXT:     %8 = "riscv.rem"(%5, %7) : (i64, i64) -> i64
// CHECK-NEXT:     %9 = "riscv.slt"(%6, %8) : (i64, i64) -> i64
// CHECK-NEXT:     %10 = "riscv.xori"(%9) : (i64) -> i64
// CHECK-NEXT: }) : () -> ()
