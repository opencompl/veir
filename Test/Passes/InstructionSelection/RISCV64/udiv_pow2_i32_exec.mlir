// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=canonicalize,instcombine,canonicalize,cse,dce,riscv > %t && veir-interpret %t | filecheck %s

// `i32` analogue of udiv_pow2_exec.mlir (`udiv_by_pow2_pattern` on `g_udivw`).
//
// CHECK is #64 (SRC is #32): isel-abi-riscv64,reconcile-cast coerces `main`'s `i32` boundary to
// `!riscv.reg`, so post-lowering the declared return type is a register.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 37 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.udiv"(%a, %b) : (i32, i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000004#32]
// CHECK: Program output: #[0x0000000000000004#64]
