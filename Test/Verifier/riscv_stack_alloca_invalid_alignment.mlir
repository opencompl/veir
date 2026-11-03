// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %slot = "riscv_stack.alloca"() <{size = 8 : i64, alignment = 3 : i64}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_stack.alloca: alignment must be a positive power of two
