// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "test", function_type = !llvm.func<void (!riscv.reg)>}> ({
  ^entry(%arg: !riscv.reg):
    "riscv_cf.return"(%arg) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected riscv_cf.return to have 0 operand(s)
