// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^entry():
      %cond = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      %t0 = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg
      %f0 = "riscv.li"() <{"value" = 20 : i64}> : () -> !riscv.reg
      %f1 = "riscv.li"() <{"value" = 30 : i64}> : () -> !riscv.reg
      %f2 = "riscv.li"() <{"value" = 40 : i64}> : () -> !riscv.reg
      // cond = 1 (nonzero) => beqz NOT taken => successor 1 (^else), falseSize = 3.
      // Segment layout [cond=1, trueSize=1, falseSize=3]; operands (cond, t0, f0, f1, f2).
      "riscv_cf.beqz"(%cond, %t0, %f0, %f1, %f2) [^then, ^else]
        <{"operandSegmentSizes" = array<i64: 1, 1, 3>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^then(%a : !riscv.reg):
      "func.return"(%a) : (!riscv.reg) -> ()
    ^else(%b0 : !riscv.reg, %b1 : !riscv.reg, %b2 : !riscv.reg):
      "func.return"(%b2) : (!riscv.reg) -> ()   // expected: f2 = 40 = 0x28
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000028#64]
