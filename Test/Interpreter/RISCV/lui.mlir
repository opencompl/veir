// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %x = "riscv.lui"() <{ value = -5 : i20 }> : () -> !reg
    %y = "riscv.lui"() <{ value = 3 : i20 }> : () -> !reg
    "func.return"(%x, %y) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffb000#64, 0x0000000000003000#64]
