// RUN: not veir-opt %s 2>&1 | filecheck %s

// As `riscv_stack_alloca_size_width_not_i64.mlir`, for `alignment`.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %slot = "riscv_stack.alloca"() <{size = 8 : i64, alignment = 8 : i16}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: alloca: expected 'alignment' to be a 64-bit signless integer attribute, but got i16
