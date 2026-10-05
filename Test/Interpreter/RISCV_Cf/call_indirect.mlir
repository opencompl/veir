// RUN: veir-interpret %s | filecheck %s

// An indirect call calls the function whose address is in its first operand.

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "foo", function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%a: !riscv.reg):
    %r = "riscv.addi"(%a) <{value = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @foo}> : () -> !llvm.ptr
    %f = "builtin.unrealized_conversion_cast"(%p) : (!llvm.ptr) -> !riscv.reg
    %c40 = "riscv.li"() <{value = 40 : i64}> : () -> !riscv.reg
    %r = "riscv_cf.call"(%f, %c40) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
