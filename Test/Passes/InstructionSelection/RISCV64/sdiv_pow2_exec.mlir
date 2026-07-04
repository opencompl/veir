// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// Functional check for `sdivPow2` (general, non-`exact`, positive and negative
// divisor): truncating (round-toward-zero) division by a constant power of two.
// `-15 sdiv 4` exercises the bias correction (a plain arithmetic shift would give
// the floor, `-4`, instead of the truncated `-3`); the `y < 0` cases exercise the
// final negation.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64)}> ({
    %pos = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %neg = "llvm.mlir.constant"() <{value = -15 : i64}> : () -> i64
    %div4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %divneg4 = "llvm.mlir.constant"() <{value = -4 : i64}> : () -> i64
    %r0 = "llvm.sdiv"(%pos, %div4) : (i64, i64) -> i64
    %r1 = "llvm.sdiv"(%neg, %div4) : (i64, i64) -> i64
    %r2 = "llvm.sdiv"(%pos, %divneg4) : (i64, i64) -> i64
    %r3 = "llvm.sdiv"(%neg, %divneg4) : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2, %r3) : (i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000003#64, 0xfffffffffffffffd#64, 0xfffffffffffffffd#64, 0x0000000000000003#64]
// CHECK: Program output: #[0x0000000000000003#64, 0xfffffffffffffffd#64, 0xfffffffffffffffd#64, 0x0000000000000003#64]
