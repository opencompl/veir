// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %b = "riscv.slliuw"(%a) <{ value = 61 : i6 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x4000000000000000#64]
