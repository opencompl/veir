// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// `riscv.la` names the symbol whose address it loads.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "main"}> ({
    %0 = "riscv.la"() <{"symbol" = @g}> : () -> !riscv.reg
    "func.return"(%0) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: %{{.*}} = "riscv.la"() <{"symbol" = @g}> : () -> !riscv.reg
