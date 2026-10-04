// RUN: veir-interpret %s | filecheck %s

// `riscv.la` loads the address of a global; a store through it is seen by a
// later load from the global.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i64, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i64}> ({
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %g = "riscv.la"() <{"symbol" = @g}> : () -> !riscv.reg
    %old = "riscv.ld"(%g) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %new = "riscv.addi"(%old) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    "riscv.sd"(%new, %g) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    %g2 = "riscv.la"() <{"symbol" = @g}> : () -> !riscv.reg
    %r = "riscv.ld"(%g2) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
