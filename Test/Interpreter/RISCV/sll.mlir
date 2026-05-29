// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 21 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.sll"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.sll"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000002a0#64, 0xa800000000000000#64]
