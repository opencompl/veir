// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Register-form rotate: the shift amount (8) is loaded from memory rather than
// a literal, so the constant recognizer does not fire and isel selects the
// register-operand riscv.ror (not rori).
// fshr(0x123456789ABCDEF0, .., 8) = rotate-right by 8 = 0xF0123456789ABCDE.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %s0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    "llvm.store"(%s0, %slot) : (i64, !llvm.ptr) -> ()
    %s = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %r = "llvm.intr.fshr"(%a, %a, %s) : (i64, i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xf0123456789abcde#64]
// CHECK: Program output: #[0xf0123456789abcde#64]

// ISEL: "riscv.ror"
// ISEL-NOT: "riscv.rori"
