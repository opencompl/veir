// RUN: not veir-opt %s 2>&1 | filecheck %s

// The forwarded operand is !riscv.reg, but the taken successor's block argument
// is i32. Segment sizes and successor-argument counts match, yet the types do
// not, so the verifier must reject this.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    ^entry():
      %cond = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      %argT = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
      %argF = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
      "riscv_cf.bnez"(%cond, %argT, %argF) [^taken, ^not_taken]
        <{"operandSegmentSizes" = array<i64: 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^taken(%yt : i32):
      "func.return"(%yt) : (i32) -> ()
    ^not_taken(%yf : i32):
      "func.return"(%yf) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.bnez: true successor argument 0 type mismatch: operand has type !riscv.reg, block argument has type i32
