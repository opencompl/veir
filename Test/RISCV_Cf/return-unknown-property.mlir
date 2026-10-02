// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = () -> ()}> ({
  ^entry():
    "riscv_cf.return"() <{unexpected}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.return: expected no properties
