// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^entry():
      %cond = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      "riscv_cf.bnez"(%cond) [^taken, ^not_taken]
        <{"operandSegmentSizes" = array<i64: 1, 0, 0>}> : (!riscv.reg) -> ()
    ^taken():
      "func.return"(%cond) : (!riscv.reg) -> ()
    ^not_taken(%x : !riscv.reg):
      "func.return"(%x) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.bnez: false operand segment expected operand count 1, got 0
