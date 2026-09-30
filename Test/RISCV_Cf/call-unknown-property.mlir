// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = () -> ()}> ({
  ^entry():
    "riscv_cf.call"() <{callee = @external, unexpected}> : () -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: expected only 'callee' property
