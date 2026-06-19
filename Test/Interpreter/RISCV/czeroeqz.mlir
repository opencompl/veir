// RUN: veir-interpret %s | filecheck %s

// czero.eqz: if condition (rs2) == 0, result is 0; otherwise result is rs1.
// %a takes the zeroed branch (cond == 0 -> 0); %b takes the pass-through
// branch (cond != 0 -> 42). Combining with a non-commutative shift
// (value %b shifted by amount %a) gives 42 << 0 = 0x2a only if both
// branches behave correctly; swapping eqz/nez semantics would not.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %val = "riscv.li"() <{ value = 42 : i64 }> : () -> !riscv.reg
    %zero = "riscv.li"() <{ value = 0 : i64 }> : () -> !riscv.reg
    %cond = "riscv.li"() <{ value = 7 : i64 }> : () -> !riscv.reg
    // condition is zero -> 0 (used as the shift amount)
    %a = "riscv.czeroeqz"(%val, %zero) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // condition is nonzero -> val (used as the shifted value)
    %b = "riscv.czeroeqz"(%val, %cond) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %res = "riscv.sll"(%b, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%res) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
