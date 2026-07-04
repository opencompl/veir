// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// Functional check for `udivPow2`: unsigned division by a constant power of two,
// including the `2^63` boundary (whose bit pattern is decoded as a negative `Int`
// even though `udiv` treats it as unsigned -- see the regression case in
// divpow2.mlir).

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %a = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %r0 = "llvm.udiv"(%a, %b) : (i64, i64) -> i64
    // (2^63 + 5) udiv 2^63 = 1
    %c = "llvm.mlir.constant"() <{value = -9223372036854775803 : i64}> : () -> i64
    %d = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %r1 = "llvm.udiv"(%c, %d) : (i64, i64) -> i64
    "func.return"(%r0, %r1) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000004#64, 0x0000000000000001#64]
// CHECK: Program output: #[0x0000000000000004#64, 0x0000000000000001#64]
