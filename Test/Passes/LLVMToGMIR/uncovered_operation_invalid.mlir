// RUN: not veir-opt %s -p=llvm-to-gmir 2>&1 | filecheck %s

// The pass fails on a module with an operation that the refinement proof of the
// branch translation does not cover, here `arith`.
// CHECK: llvm-to-gmir: the refinement proof does not cover an operation of the module

"builtin.module"() ({
  "func.func"() <{"function_type" = () -> (i64), "sym_name" = "f"}> ({
    %x = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
    "llvm.br"(%x) [^bb1] : (i64) -> ()
  ^bb1(%y: i64):
    "func.return"(%y) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
