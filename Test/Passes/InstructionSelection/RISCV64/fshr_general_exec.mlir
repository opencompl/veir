// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// General (distinct-operand) funnel shift right: not a rotate, so it lowers to the
// shift/or expansion (slli 1 / sll ~z / srl / or), mirroring LLVM. The shift amount
// (8) is loaded from memory so the expansion is not constant-folded.
// fshr(0x123456789ABCDEF0, 0xFEDCBA9876543210, 8)
//   = (x << 56) | (y >> 8) = 0xF0FEDCBA98765432.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = -81985529216486896 : i64}> : () -> i64
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %s0 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    "llvm.store"(%s0, %slot) : (i64, !llvm.ptr) -> ()
    %s = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %r = "llvm.intr.fshr"(%a, %b, %s) : (i64, i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xf0fedcba98765432#64]
// CHECK: Program output: #[0xf0fedcba98765432#64]

// ISEL: "riscv.srl"
// ISEL-NOT: "riscv.ror"
