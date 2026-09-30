// RUN: veir-interpret %s | filecheck %s

// Executing `riscv_cf.unreachable` is immediate undefined behaviour, as for
// `llvm.unreachable`.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^1():
      %zero = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      "riscv_cf.bnez"(%zero, %zero) [^2, ^3] <{"operandSegmentSizes" = array<i64: 1, 1, 0>}> : (!riscv.reg, !riscv.reg) -> ()
    ^2(%t : !riscv.reg):
      "func.return"(%t) : (!riscv.reg) -> ()
    ^3():
      "riscv_cf.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
