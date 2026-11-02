// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// Stack-passed call arguments are not lowered.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "too_many_args", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a: !riscv.reg):
    "riscv_cf.call"(%a, %a, %a, %a, %a, %a, %a, %a, %a) <{callee = @external}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @too_many_args: riscv_cf.call with 9 arguments and 0 results is not supported
