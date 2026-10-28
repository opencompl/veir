// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// smin(-1, 1) = -1 (signed); distinct from umin. -> riscv.min
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    // Round-trip %a through memory so it is not a constant; otherwise the op
    // under test is folded away during lowering.
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %a0 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    "llvm.store"(%a0, %slot) : (i64, !llvm.ptr) -> ()
    %a = "llvm.load"(%slot) : (!llvm.ptr) -> i64
    %b = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.intr.smin"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0xffffffffffffffff#64]
// CHECK: Program output: #[0xffffffffffffffff#64]

// ISEL: "riscv.min"
