// RUN: veir-interpret %s | filecheck %s

// In i1, -1 is also intMin, so `srem -1, -1` is immediate UB.
"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %one = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i1
    %y = "llvm.srem"(%one, %one) : (i1, i1) -> i1
    "func.return"(%y) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
