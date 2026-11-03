// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// smax(-1, 1) = 1 (signed); distinct from umax. -> riscv.max
// The constants are frozen so that the combiner does not fold the min/max away.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a_c = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %a = "llvm.freeze"(%a_c) : (i64) -> i64
    %b_c = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %b = "llvm.freeze"(%b_c) : (i64) -> i64
    %r = "llvm.intr.smax"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000001#64]
// CHECK: Program output: #[0x0000000000000001#64]

// ISEL: "riscv.max"
