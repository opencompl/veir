// RUN: not veir-interpret %s 2>&1 | filecheck %s

// Moving a poison pointer into a riscv register is not yet supported.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %r = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error while interpreting module
