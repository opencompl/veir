// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// umax(-1, 1) = -1 (unsigned, 0xff..ff is the larger). -> riscv.maxu
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %a = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.intr.umax"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xffffffffffffffff#64]
// CHECK: Program output: #[0xffffffffffffffff#64]

// ISEL: "riscv.maxu"
