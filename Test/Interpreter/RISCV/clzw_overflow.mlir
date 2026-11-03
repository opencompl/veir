// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !riscv.reg
    %b = "riscv.clzw"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%b) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001f#64]
