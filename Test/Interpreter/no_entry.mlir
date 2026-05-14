// RUN: veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i1 ()>, sym_name = "f"}> ({
  ^bb0():
    %c0 = "llvm.mlir.constant"() <{"value" = 0 : i1}> : () -> i1
    "llvm.return"(%c0) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error: Expected executable operations at module level or a zero-argument function named main()
