// RUN: veir-interpret %s | filecheck %s

// In i1, -1 is also intMin, so `sdiv -1, -1` is immediate UB.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i1}> ({
    %one = "llvm.mlir.constant"() <{ "value" = -1 : i1 }> : () -> i1
    %y = "llvm.sdiv"(%one, %one) : (i1, i1) -> i1
    "func.return"(%y) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
