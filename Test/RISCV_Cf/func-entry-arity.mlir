// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg) -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: entry block must have 1 arguments to match function signature
