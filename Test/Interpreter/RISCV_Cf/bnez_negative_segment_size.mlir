// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^entry():
      %cond = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      %arg = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
      "riscv_cf.bnez"(%cond, %arg) [^taken, ^not_taken]
        <{"operandSegmentSizes" = array<i64: 1, -1, 2>}> : (!riscv.reg, !riscv.reg) -> ()
    ^taken():
      "func.return"(%cond) : (!riscv.reg) -> ()
    ^not_taken():
      "func.return"(%cond) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.bnez: operandSegmentSizes contains negative size -1
