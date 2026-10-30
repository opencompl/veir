// RUN: veir-opt %s --print-op-generic -p=register-allocation-riscv64 | filecheck %s

"builtin.module"() ({}) : () -> ()

// CHECK-LABEL: "builtin.module"() ({}) : () -> ()
// CHECK-NOT:   "riscv_cf.func"
