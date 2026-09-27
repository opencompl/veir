// RUN: veir-interpret %s | filecheck %s

// A register has no poison, so a poison pointer may be cast to any register
// value. The interpreter picks 0, as it does for a poison integer.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %r = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
