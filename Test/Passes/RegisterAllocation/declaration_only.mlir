// RUN: veir-opt %s --print-op-generic -p=register-allocation-riscv64 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "external", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()
}) : () -> ()

// CHECK: "riscv_cf.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "external"}> ({}) : () -> ()
// CHECK-NOT: !riscv.reg<j
