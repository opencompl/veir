// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %slot = "riscv_stack.alloca"() <{size = 8 : i32, alignment = 8 : i64}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: alloca: expected 'size' to be a 64-bit signless integer attribute, but got i32
