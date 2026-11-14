// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// -1 * 2 is -2, whose high half is all ones; read unsigned the same bits are
// 2^64-1, and (2^64-1) * 2 has high half 1. -> riscv.mulh and riscv.mulhu.
// The constants are frozen so that the combiner does not fold the products away.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %a_c = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %a = "llvm.freeze"(%a_c) : (i64) -> i64
    %b_c = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %b = "llvm.freeze"(%b_c) : (i64) -> i64
    %s = "llvm.intr.smulh"(%a, %b) : (i64, i64) -> i64
    %u = "llvm.intr.umulh"(%a, %b) : (i64, i64) -> i64
    "func.return"(%s, %u) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xffffffffffffffff#64, 0x0000000000000001#64]
// CHECK: Program output: #[0xffffffffffffffff#64, 0x0000000000000001#64]

// ISEL: "riscv.mulh"
// ISEL: "riscv.mulhu"
