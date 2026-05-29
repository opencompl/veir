// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 0 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 1 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -1 : i64 }> : () -> !reg
    %d = "riscv.sltz"(%a) : (!reg) -> !reg
    %e = "riscv.sltz"(%b) : (!reg) -> !reg
    %f = "riscv.sltz"(%c) : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000000#64, 0x0000000000000001#64]
