// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Register-form rotate: the shift amount (8) is loaded back from a stack slot
// rather than being a constant, which the post-legalizer combiner would fold,
// so the constant recognizer does not fire and isel selects the
// register-operand riscv.rol (not rori).
// fshl(0x123456789ABCDEF0, .., 8) = rotate-left by 8 = 0x3456789ABCDEF012.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %slot = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%eight, %slot) : (i64, !llvm.ptr) -> ()
    %s = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %r = "llvm.intr.fshl"(%a, %a, %s) : (i64, i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x3456789abcdef012#64]
// CHECK: Program output: #[0x3456789abcdef012#64]

// ISEL: "riscv.rol"
// ISEL-NOT: "riscv.rori"
