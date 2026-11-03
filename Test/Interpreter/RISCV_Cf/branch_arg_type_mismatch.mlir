// RUN: not veir-opt %s 2>&1 | filecheck %s

// The branch operand is !riscv.reg, but the successor block argument is i32.
// Operand and successor-argument counts match, yet the types do not, so the
// verifier must reject this.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    ^entry():
      %x = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
      "riscv_cf.branch"(%x) [^dest] : (!riscv.reg) -> ()
    ^dest(%y : i32):
      "func.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.branch: successor argument 0 type mismatch: operand has type !riscv.reg, block argument has type i32
