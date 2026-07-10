// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,riscv-combine,reconcile-cast,dce > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64)}> ({
    %i64max = "llvm.mlir.constant"() <{value = 9223372036854775807 : i64}> : () -> i64
    %i64min = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %negone = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %pos_shl_overflow = "llvm.mlir.constant"() <{value = 4611686018427387904 : i64}> : () -> i64

    %sadd = "llvm.intr.sadd.sat"(%i64max, %one) : (i64, i64) -> i64
    %ssub = "llvm.intr.ssub.sat"(%i64min, %one) : (i64, i64) -> i64
    %uadd = "llvm.intr.uadd.sat"(%negone, %one) : (i64, i64) -> i64
    %usub = "llvm.intr.usub.sat"(%zero, %one) : (i64, i64) -> i64
    %sshl = "llvm.intr.sshl.sat"(%pos_shl_overflow, %one) : (i64, i64) -> i64
    %ushl = "llvm.intr.ushl.sat"(%negone, %one) : (i64, i64) -> i64

    "func.return"(%sadd, %ssub, %uadd, %usub, %sshl, %ushl) : (i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x7fffffffffffffff#64, 0x8000000000000000#64, 0xffffffffffffffff#64, 0x0000000000000000#64, 0x7fffffffffffffff#64, 0xffffffffffffffff#64]
// CHECK: Program output: #[0x7fffffffffffffff#64, 0x8000000000000000#64, 0xffffffffffffffff#64, 0x0000000000000000#64, 0x7fffffffffffffff#64, 0xffffffffffffffff#64]

// ISEL: "riscv.czeroeqz"
// ISEL: "riscv.minu"
// ISEL: "riscv.maxu"
// ISEL: "riscv.sltiu"
