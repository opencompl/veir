// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.slti"(%a) <{ value = 33 : i12 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %d = "riscv.slti"(%c) <{ value = -33 : i12 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
