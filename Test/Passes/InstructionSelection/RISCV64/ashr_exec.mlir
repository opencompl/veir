// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %r = "llvm.ashr"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x000000000000000a#64]
// CHECK: Program output: #[0x000000000000000a#64]
