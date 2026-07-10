// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// General (distinct-operand) funnel shift left: not a rotate, so it lowers to the
// shift/or expansion (sll / srli 1 / srl ~z / or), mirroring LLVM.
// fshl(0x123456789ABCDEF0, 0xFEDCBA9876543210, 8)
//   = (x << 8) | (y >> 56) = 0x3456789ABCDEF0FE.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = 1311768467463790320 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = -81985529216486896 : i64}> : () -> i64
    %x = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %y = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %s = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.intr.fshl"(%a, %b, %s) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x3456789abcdef0fe#64]
// CHECK: Program output: #[0x3456789abcdef0fe#64]

// ISEL: "riscv.sll"
// ISEL-NOT: "riscv.rol"
