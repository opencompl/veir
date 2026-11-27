// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %1 = "riscv_regalloc.spill"(%0) : (!riscv.reg) -> !riscv.stack
      %2 = "riscv_regalloc.reload"(%1) : (!riscv.stack) -> !riscv.reg
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      [[A:%[0-9]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
// CHECK-NEXT: [[B:%[0-9]+]] = "riscv_regalloc.spill"([[A]]) : (!riscv.reg) -> !riscv.stack
// CHECK-NEXT: %{{[0-9]+}} = "riscv_regalloc.reload"([[B]]) : (!riscv.stack) -> !riscv.reg
