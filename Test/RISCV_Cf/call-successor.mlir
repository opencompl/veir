// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = () -> ()}> ({
  ^entry():
    "riscv_cf.call"() [^exit] <{callee = @external}> : () -> ()
  ^exit():
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: Expected 0 successors
