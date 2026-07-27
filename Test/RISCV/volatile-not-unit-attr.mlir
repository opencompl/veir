// RUN: not veir-opt %s 2>&1 | filecheck %s

// 'volatile_' is a unit attribute, matching the LLVM dialect's spelling; giving
// it a value is an error rather than being read as a truthy flag.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "main"}> ({
    ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
      "riscv.sd"(%val, %addr) <{"value" = 0 : i12, "volatile_" = 1 : i64}> : (!riscv.reg, !riscv.reg) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: expected 'volatile_' to be an optional unit attribute, but got 1 : i64
