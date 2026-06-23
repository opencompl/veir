// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// Regression test for a bug in isel-br-riscv64 where block-argument operands
// passed across a branch were emitted in reverse order, so the successor block
// received its arguments swapped. Here ^36 should bind %a0 = 111 and %a1 = 52;
// returning %a1 must yield 52 both when interpreted directly and after lowering.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %0 = "llvm.mlir.constant"() <{value = 111 : i64}> : () -> i64
      %1 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
      "llvm.br"(%0, %1) [^bb1] : (i64, i64) -> ()
    ^bb1(%a0 : i64, %a1 : i64):
      "llvm.return"(%a1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000034#64]
// CHECK: Program output: #[0x0000000000000034#64]
