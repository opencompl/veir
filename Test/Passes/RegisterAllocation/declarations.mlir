// RUN: veir-opt %s --print-op-generic -p=register-allocation-riscv64 | filecheck %s

// Declarations with arguments/results are skipped, before and between bodies.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "external_before", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "external_between", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "external_before"
// CHECK-SAME:  }> ({}) : () -> ()
// CHECK-LABEL: "sym_name" = "f"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()
// CHECK-LABEL: "sym_name" = "external_between"
// CHECK-SAME:  }> ({}) : () -> ()
// CHECK-LABEL: "sym_name" = "g"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()
