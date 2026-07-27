// RUN: VEIR_ROUNDTRIP

// The RISC-V memory operations carry a `volatile_` flag alongside their offset
// immediate. Like the LLVM dialect's `volatile_`, it is printed only when set,
// so an ordinary access is indistinguishable from one on a dialect without the
// flag at all.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "main"}> ({
    ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
      // Volatile loads, one per width.
      %0 = "riscv.ld"(%addr) <{"value" = 0 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %1 = "riscv.lw"(%addr) <{"value" = 4 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %2 = "riscv.lwu"(%addr) <{"value" = 8 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %3 = "riscv.lh"(%addr) <{"value" = 12 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %4 = "riscv.lhu"(%addr) <{"value" = 14 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %5 = "riscv.lb"(%addr) <{"value" = 16 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      %6 = "riscv.lbu"(%addr) <{"value" = 17 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
      // Volatile stores, one per width.
      "riscv.sd"(%val, %addr) <{"value" = 0 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sw"(%val, %addr) <{"value" = 8 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sh"(%val, %addr) <{"value" = 12 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sb"(%val, %addr) <{"value" = 16 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
      // The same accesses without the flag: nothing extra may appear.
      %7 = "riscv.ld"(%addr) <{"value" = 0 : i12}> : (!riscv.reg) -> !riscv.reg
      %8 = "riscv.lbu"(%addr) <{"value" = 17 : i12}> : (!riscv.reg) -> !riscv.reg
      "riscv.sd"(%val, %addr) <{"value" = 0 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "riscv.sb"(%val, %addr) <{"value" = 16 : i12}> : (!riscv.reg, !riscv.reg) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (!riscv.reg, !riscv.reg) -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : !riscv.reg, %{{.*}} : !riscv.reg):
// CHECK-NEXT:         %{{.*}} = "riscv.ld"(%{{.*}}) <{"value" = 0 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lw"(%{{.*}}) <{"value" = 4 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lwu"(%{{.*}}) <{"value" = 8 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lh"(%{{.*}}) <{"value" = 12 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lhu"(%{{.*}}) <{"value" = 14 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lb"(%{{.*}}) <{"value" = 16 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lbu"(%{{.*}}) <{"value" = 17 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv.sd"(%{{.*}}, %{{.*}}) <{"value" = 0 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sw"(%{{.*}}, %{{.*}}) <{"value" = 8 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sh"(%{{.*}}, %{{.*}}) <{"value" = 12 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sb"(%{{.*}}, %{{.*}}) <{"value" = 16 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         %{{.*}} = "riscv.ld"(%{{.*}}) <{"value" = 0 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         %{{.*}} = "riscv.lbu"(%{{.*}}) <{"value" = 17 : i12}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:         "riscv.sd"(%{{.*}}, %{{.*}}) <{"value" = 0 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "riscv.sb"(%{{.*}}, %{{.*}}) <{"value" = 16 : i12}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
