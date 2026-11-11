// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg<x0>)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %a = "builtin.unrealized_conversion_cast"(%one) : (i64) -> !riscv.reg<x0>
    "func.return"(%a) : (!riscv.reg<x0>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
