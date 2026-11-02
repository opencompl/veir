// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// A leftover cast means a value was never lowered to a register.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<!riscv.reg (!riscv.reg)>, sym_name = "main"}> ({
  ^bb0(%x: !riscv.reg):
    %i = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i64
    %r = "builtin.unrealized_conversion_cast"(%i) : (i64) -> !riscv.reg
    "riscv_cf.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @main: unlowered operation 'builtin.unrealized_conversion_cast'
