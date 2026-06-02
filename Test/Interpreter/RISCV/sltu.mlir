// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = -13 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 7 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -7 : i64 }> : () -> !reg
    %d = "riscv.sltu"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.sltu"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000001#64]

