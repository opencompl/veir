// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// General (distinct-operand) funnel shift left: not a rotate, so it lowers to the
// shift/or expansion (sll / srli 1 / srl ~z / or), mirroring LLVM. The shift amount
// (8) is loaded from memory so the expansion is not constant-folded.
// fshl(0x123456789ABCDEF0, 0xFEDCBA9876543210, 8)
//   = (x << 8) | (y >> 56) = 0x3456789ABCDEF0FE.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = -81985529216486896 : i64}> : () -> i64
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %s0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    "llvm.store"(%s0, %slot) : (i64, !llvm.ptr) -> ()
    %s = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %r = "llvm.intr.fshl"(%a, %b, %s) : (i64, i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x3456789abcdef0fe#64]
// CHECK: Program output: #[0x3456789abcdef0fe#64]

// ISEL: "riscv.sll"
// ISEL-NOT: "riscv.rol"
