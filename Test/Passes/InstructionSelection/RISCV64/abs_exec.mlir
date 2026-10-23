// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// abs(-5) = 5 and abs(INT64_MIN) = INT64_MIN. -> riscv.neg + riscv.max
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %a = "llvm.mlir.constant"() <{value = -5 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %r0 = "llvm.intr.abs"(%a) <{is_int_min_poison = false}> : (i64) -> i64
    %r1 = "llvm.intr.abs"(%b) <{is_int_min_poison = false}> : (i64) -> i64
    "func.return"(%r0, %r1) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000005#64, 0x8000000000000000#64]
// CHECK: Program output: #[0x0000000000000005#64, 0x8000000000000000#64]

// ISEL: "riscv.neg"
// ISEL: "riscv.max"
