// RUN: not veir-opt %s 2>&1 | filecheck %s
"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = (i64) -> ()}> ({
  ^bb0(%x: i64):
    %r = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %bad = "riscv.brev8"(%r) : (!riscv.reg) -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
// CHECK: Expected result 0 to have !riscv.reg type
