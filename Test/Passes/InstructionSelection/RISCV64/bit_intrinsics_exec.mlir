// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64)}> ({
    %x = "llvm.mlir.constant"() <{value = 0x0123456789abcdef : i64}> : () -> i64
    %ctlz = "llvm.intr.ctlz"(%x) <{is_zero_poison = false}> : (i64) -> i64
    %ctlz_poison = "llvm.intr.ctlz"(%x) <{is_zero_poison = true}> : (i64) -> i64
    %cttz = "llvm.intr.cttz"(%x) <{is_zero_poison = false}> : (i64) -> i64
    %cttz_poison = "llvm.intr.cttz"(%x) <{is_zero_poison = true}> : (i64) -> i64
    %ctpop = "llvm.intr.ctpop"(%x) : (i64) -> i64
    %bswap = "llvm.intr.bswap"(%x) : (i64) -> i64
    %bitreverse = "llvm.intr.bitreverse"(%x) : (i64) -> i64
    "func.return"(%ctlz, %ctlz_poison, %cttz, %cttz_poison, %ctpop, %bswap, %bitreverse) : (i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:      Program output: #[0x0000000000000007#64, 0x0000000000000007#64, 0x0000000000000000#64, 0x0000000000000000#64, 0x0000000000000020#64, 0xefcdab8967452301#64, 0xf7b3d591e6a2c480#64]

// CHECK:    "riscv.clz"
// CHECK:    "riscv.ctz"
// CHECK:    "riscv.cpop"
// CHECK:    "riscv.rev8"
// CHECK:    "riscv.slli"
// CHECK:    "riscv.srli"
// CHECK:    "riscv.rev8"

// CHECK:    Program output: #[0x0000000000000007#64, 0x0000000000000007#64, 0x0000000000000000#64, 0x0000000000000000#64, 0x0000000000000020#64, 0xefcdab8967452301#64, 0xf7b3d591e6a2c480#64]
