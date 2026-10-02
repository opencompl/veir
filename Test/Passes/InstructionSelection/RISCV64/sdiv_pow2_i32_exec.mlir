// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,isel-abi-riscv64,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// `i32` analogue of sdiv_pow2_exec.mlir (`sdivwPow2`, general non-`exact` form).
// The RISC-V psABI returns an `i32` sign-extended to 64 bits, hence CHECK's
// `0xfffffffffffffffd` for SRC's `0xfffffffd`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32)}> ({
    %neg = "llvm.mlir.constant"() <{value = -15 : i32}> : () -> i32
    %div4 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %divneg4 = "llvm.mlir.constant"() <{value = -4 : i32}> : () -> i32
    %r0 = "llvm.sdiv"(%neg, %div4) : (i32, i32) -> i32
    %r1 = "llvm.sdiv"(%neg, %divneg4) : (i32, i32) -> i32
    "func.return"(%r0, %r1) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xfffffffd#32, 0x00000003#32]
// CHECK: Program output: #[0xfffffffffffffffd#64, 0x0000000000000003#64]
