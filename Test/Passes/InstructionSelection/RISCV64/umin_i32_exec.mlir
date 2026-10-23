// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// umin(-1, 1) = 1 and umax(-1, 1) = -1 (unsigned) at `i32`: widening with sext preserves the
// unsigned order.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32)}> ({
    %a = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %r0 = "llvm.intr.umin"(%a, %b) : (i32, i32) -> i32
    %r1 = "llvm.intr.umax"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r0, %r1) : (i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000001#32, 0xffffffff#32]
// CHECK: Program output: #[0x00000001#32, 0xffffffff#32]

// ISEL: "riscv.minu"
// ISEL: "riscv.maxu"
