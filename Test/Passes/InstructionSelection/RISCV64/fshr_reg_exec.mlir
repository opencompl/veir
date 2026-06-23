// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s

// Register-form rotate: the shift amount is computed (5 + 3 = 8) rather than a
// literal, so the constant recognizer does not fire and isel selects the
// register-operand riscv.ror (not rori).
// fshr(0x123456789ABCDEF0, .., 8) = rotate-right by 8 = 0xF0123456789ABCDE.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %x = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %y = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %s = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.intr.fshr"(%a, %a, %s) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xf0123456789abcde#64]
// CHECK: Program output: #[0xf0123456789abcde#64]
