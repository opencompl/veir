// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !reg
    %b = "riscv.clzw"(%a) : (!reg) -> !reg
    "func.return"(%b) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001f#64]
