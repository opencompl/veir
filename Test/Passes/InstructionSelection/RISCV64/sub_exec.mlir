// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=riscv > %t && veir-interpret %t | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = 70 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %r = "llvm.sub"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000032#64]
// CHECK: Program output: #[0x0000000000000032#64]
