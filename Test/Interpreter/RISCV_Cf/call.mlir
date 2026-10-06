// RUN: veir-interpret %s | filecheck %s

// A direct call passes its register operands to the callee and binds the register it returns.

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "foo", function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%a: !riscv.reg):
    %r = "riscv.addi"(%a) <{value = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %c40 = "riscv.li"() <{value = 40 : i64}> : () -> !riscv.reg
    %r = "riscv_cf.call"(%c40) <{callee = @foo}> : (!riscv.reg) -> !riscv.reg
    "riscv_cf.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
