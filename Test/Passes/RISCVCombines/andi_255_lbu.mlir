// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `lbu` already clears bits 63:8, so an `andi 255` of it is removed. Another
// mask, or a mask of a sign-extending `lb`, is kept.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "andi_255_lbu"}> ({
  ^bb0(%addr: !riscv.reg):
    %unsigned = "riscv.lbu"(%addr) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %masked = "riscv.andi"(%unsigned) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %low = "riscv.andi"(%unsigned) <{"value" = 127 : i64}> : (!riscv.reg) -> !riscv.reg
    %signed = "riscv.lb"(%addr) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
    %signed_masked = "riscv.andi"(%signed) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%masked, %low, %signed_masked) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @andi_255_lbu(
// CHECK: %[[UNSIGNED:[^ ]*]] = "riscv.lbu"(%{{[^)]*}}) <{"value" = 3 : i64}>
// CHECK-NEXT: %[[LOW:[^ ]*]] = "riscv.andi"(%[[UNSIGNED]]) <{"value" = 127 : i64}>
// CHECK-NEXT: %[[SIGNED:[^ ]*]] = "riscv.lb"(%{{[^)]*}}) <{"value" = 5 : i64}>
// CHECK-NEXT: %[[SMASKED:[^ ]*]] = "riscv.andi"(%[[SIGNED]]) <{"value" = 255 : i64}>
// CHECK-NEXT: "func.return"(%[[UNSIGNED]], %[[LOW]], %[[SMASKED]])
