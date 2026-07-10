// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// Functional check for `sdivPow2Exact` (positive and negative divisor): evenly
// divisible signed division by a constant power of two, using the `exact` flag.
// Since the division is exact, the plain arithmetic-shift fast path agrees with
// full truncating division (no bias correction needed).

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64)}> ({
    %pos = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %neg = "llvm.mlir.constant"() <{value = -16 : i64}> : () -> i64
    %div4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %divneg4 = "llvm.mlir.constant"() <{value = -4 : i64}> : () -> i64
    %r0 = "llvm.sdiv"(%pos, %div4) <{exact}> : (i64, i64) -> i64
    %r1 = "llvm.sdiv"(%neg, %div4) <{exact}> : (i64, i64) -> i64
    %r2 = "llvm.sdiv"(%pos, %divneg4) <{exact}> : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2) : (i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000004#64, 0xfffffffffffffffc#64, 0xfffffffffffffffc#64]
// CHECK: Program output: #[0x0000000000000004#64, 0xfffffffffffffffc#64, 0xfffffffffffffffc#64]
