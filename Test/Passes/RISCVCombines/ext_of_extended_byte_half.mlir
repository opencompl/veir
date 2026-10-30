// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// A byte or half-word extension of a value that it leaves unchanged is removed: narrow loads of the
// same kind, and an `andi` whose immediate clears the sign bit. `sext.b (andi x, 128)` keeps bit 7,
// so its extension stays.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "ext_of_extended"}> ({
  ^bb0(%addr: !riscv.reg):
    %b = "riscv.lb"(%addr) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %sb = "riscv.sextb"(%b) : (!riscv.reg) -> !riscv.reg
    %h = "riscv.lh"(%addr) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    %sh = "riscv.sexth"(%h) : (!riscv.reg) -> !riscv.reg
    %hu = "riscv.lhu"(%addr) <{"value" = 4 : i64}> : (!riscv.reg) -> !riscv.reg
    %zh = "riscv.zexth"(%hu) : (!riscv.reg) -> !riscv.reg
    %small = "riscv.andi"(%addr) <{"value" = 64 : i64}> : (!riscv.reg) -> !riscv.reg
    %ssmall = "riscv.sextb"(%small) : (!riscv.reg) -> !riscv.reg
    %big = "riscv.andi"(%addr) <{"value" = 128 : i64}> : (!riscv.reg) -> !riscv.reg
    %sbig = "riscv.sextb"(%big) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sb, %sh, %zh, %ssmall, %sbig) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[B:[^ ]*]] = "riscv.lb"
// CHECK:      %[[H:[^ ]*]] = "riscv.lh"
// CHECK:      %[[HU:[^ ]*]] = "riscv.lhu"
// CHECK:      %[[SMALL:[^ ]*]] = "riscv.andi"{{.*}}<{"value" = 64 : i64}>
// CHECK:      %[[BIG:[^ ]*]] = "riscv.andi"{{.*}}<{"value" = 128 : i64}>
// CHECK-NEXT: %[[SBIG:[^ ]*]] = "riscv.sextb"(%[[BIG]])
// CHECK:      "func.return"(%[[B]], %[[H]], %[[HU]], %[[SMALL]], %[[SBIG]])
