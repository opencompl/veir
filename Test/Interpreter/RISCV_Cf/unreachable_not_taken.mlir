// RUN: veir-interpret %s | filecheck %s

// A `riscv_cf.unreachable` that is never reached does not make the program
// undefined.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^1():
      %one = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      "riscv_cf.bnez"(%one, %one) [^2, ^3] <{"operandSegmentSizes" = array<i64: 1, 1, 0>}> : (!riscv.reg, !riscv.reg) -> ()
    ^2(%t : !riscv.reg):
      "func.return"(%t) : (!riscv.reg) -> ()
    ^3():
      "riscv_cf.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
