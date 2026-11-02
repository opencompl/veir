// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// RISC-V code must live in an `llvm.func` or `riscv_cf.func`.
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: function @main: 'func.func' is not supported; functions must be llvm.func or riscv_cf.func
