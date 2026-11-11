// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg<x0>)}> ({
    %a = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg<x0>
    "func.return"(%a) : (!riscv.reg<x0>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
