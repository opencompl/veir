// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^entry():
      %cond = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      %a = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
      %b = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
      %c = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
      // cond = 1 (nonzero) => bnez taken => successor 0 (^taken).
      // Segment layout [cond=1, trueSize=2, falseSize=1]; operands (cond, a, b, c).
      "riscv_cf.bnez"(%cond, %a, %b, %c) [^taken, ^not_taken]
        <{"operandSegmentSizes" = array<i64: 1, 2, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^taken(%t0 : !riscv.reg, %t1 : !riscv.reg):
      "func.return"(%t1) : (!riscv.reg) -> ()   // expected: b = 8 = 0x8
    ^not_taken(%f0 : !riscv.reg):
      "func.return"(%f0) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64]
