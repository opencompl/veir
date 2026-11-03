// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

"builtin.module"() ({
  "riscv_cf.func"() <{function_type = (!riscv.reg) -> (), sym_name = "main"}> ({
  ^bb0(%x: !riscv.reg):
    %i = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i64
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @main: unlowered operation 'builtin.unrealized_conversion_cast'
