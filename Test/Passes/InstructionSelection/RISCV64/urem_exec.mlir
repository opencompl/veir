// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=riscv | veir-interpret | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = 90 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %r = "llvm.urem"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x000000000000000a#64]
// CHECK: Program output: #[0x000000000000000a#64]
