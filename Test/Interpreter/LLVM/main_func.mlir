// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i1 ()>, sym_name = "main"}> ({
  ^bb0():
    %c0 = "llvm.mlir.constant"() <{"value" = 0 : i1}> : () -> i1
    %c1 = "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
    %v0 = "llvm.add"(%c0, %c1) : (i1, i1) -> i1
    "llvm.br"() [^bb1] : () -> ()

  ^bb1():
    "llvm.return"(%v0) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1#1]
