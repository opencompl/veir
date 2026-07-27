// RUN: veir2mir %s | filecheck %s

// Volatile RISC-V memory operations become MIR instructions with volatile
// MachineMemOperands. Plain accesses remain unannotated.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> i64, sym_name = "main"}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %ld = "riscv.ld"(%addr) <{"value" = 0 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lw = "riscv.lw"(%addr) <{"value" = 4 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lwu = "riscv.lwu"(%addr) <{"value" = 8 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lh = "riscv.lh"(%addr) <{"value" = 12 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lhu = "riscv.lhu"(%addr) <{"value" = 14 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lb = "riscv.lb"(%addr) <{"value" = 16 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    %lbu = "riscv.lbu"(%addr) <{"value" = 17 : i12, volatile_}> : (!riscv.reg) -> !riscv.reg
    "riscv.sd"(%val, %addr) <{"value" = 0 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sw"(%val, %addr) <{"value" = 8 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sh"(%val, %addr) <{"value" = 12 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sb"(%val, %addr) <{"value" = 16 : i12, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
    %plain = "riscv.ld"(%addr) <{"value" = 24 : i12}> : (!riscv.reg) -> !riscv.reg
    "riscv.sd"(%val, %addr) <{"value" = 32 : i12}> : (!riscv.reg, !riscv.reg) -> ()
    %ret = "builtin.unrealized_conversion_cast"(%ld) : (!riscv.reg) -> i64
    "func.return"(%ret) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      = LD {{.*}}, 0 :: (volatile load (s64))
// CHECK-NEXT: {{.*}} = LW {{.*}}, 4 :: (volatile load (s32))
// CHECK-NEXT: {{.*}} = LWU {{.*}}, 8 :: (volatile load (s32))
// CHECK-NEXT: {{.*}} = LH {{.*}}, 12 :: (volatile load (s16))
// CHECK-NEXT: {{.*}} = LHU {{.*}}, 14 :: (volatile load (s16))
// CHECK-NEXT: {{.*}} = LB {{.*}}, 16 :: (volatile load (s8))
// CHECK-NEXT: {{.*}} = LBU {{.*}}, 17 :: (volatile load (s8))
// CHECK-NEXT: SD {{.*}}, {{.*}}, 0 :: (volatile store (s64))
// CHECK-NEXT: SW {{.*}}, {{.*}}, 8 :: (volatile store (s32))
// CHECK-NEXT: SH {{.*}}, {{.*}}, 12 :: (volatile store (s16))
// CHECK-NEXT: SB {{.*}}, {{.*}}, 16 :: (volatile store (s8))
// CHECK-NEXT: {{.*}} = LD {{.*}}, 24{{$}}
// CHECK-NEXT: SD {{.*}}, {{.*}}, 32{{$}}
