// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = () -> ()}> ({
  ^entry():
    %r = "riscv_cf.call"() <{callee = @external}> : () -> i64
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: Expected result 0 to have !riscv.reg type
