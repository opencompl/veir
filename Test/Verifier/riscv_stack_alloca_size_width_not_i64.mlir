// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_stack.alloca`'s `size` and `alignment` are `BitVec 64`, so a declared
// width other than i64 is rejected at the parse boundary rather than stored and
// then ignored. Nothing exercised this before: the width check lived in the
// verifier and no test reached it.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %slot = "riscv_stack.alloca"() <{size = 8 : i32, alignment = 8 : i64}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: alloca: expected 'size' to be a 64-bit signless integer attribute, but got i32
