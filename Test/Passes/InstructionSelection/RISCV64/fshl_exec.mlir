// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// fshl(0x123456789ABCDEF0, .., 8) = rotate-left by 8 = 0x3456789ABCDEF012
// (the top byte 0x12 wraps around to the bottom); constant amount -> riscv.rori
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    // Round-trip %a through memory so it is not a constant; otherwise the
    // rotate is folded away during lowering.
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %a0 = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    "llvm.store"(%a0, %slot) : (i64, !llvm.ptr) -> ()
    %a = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %s = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %r = "llvm.intr.fshl"(%a, %a, %s) : (i64, i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x3456789abcdef012#64]
// CHECK: Program output: #[0x3456789abcdef012#64]

// ISEL: "riscv.rori"
