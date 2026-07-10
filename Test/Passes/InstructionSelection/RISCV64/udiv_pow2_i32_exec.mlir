// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// `i32` analogue of udiv_pow2_exec.mlir (`udivwPow2`).
//
// CHECK is #64 (SRC is #32): reconcile-cast coerces `main`'s `i32` boundary to
// `!riscv.reg`, so post-lowering the declared return type is a register.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %a = "llvm.mlir.constant"() <{value = 37 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.udiv"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000004#32]
// CHECK: Program output: #[0x0000000000000004#64]
