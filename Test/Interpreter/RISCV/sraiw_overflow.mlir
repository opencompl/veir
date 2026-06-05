// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 4294967296 : i64 }> : () -> !riscv.reg
    %b = "riscv.sraiw"(%a) <{ value = 3 : i5 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
