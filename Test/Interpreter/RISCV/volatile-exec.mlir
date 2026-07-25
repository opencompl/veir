// RUN: veir-interpret %s | filecheck %s

// The volatile flag constrains what the *optimizer* may do; it does not change
// what an access computes. This mirrors `ld-sd.mlir` with every memory op marked
// volatile, and must produce the same result.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%x, %a) <{ "value" = 0 : i64, volatile_ }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64, volatile_ }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000122#64]
