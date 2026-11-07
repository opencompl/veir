// RUN: veir-opt %s --print-op-generic -p=register-allocation-riscv64 | filecheck %s

// A non-function sibling must not prevent allocation of later functions.
"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64,
    global_type = i32, linkage = #llvm.linkage<external>, sym_name = "global",
    value = 41 : i32}> ({}) : () -> ()
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "llvm.mlir.global"()
// CHECK-SAME:  "sym_name" = "global"
// CHECK-SAME:  "value" = 41 : i32
// CHECK-SAME:  }> ({}) : () -> ()
// CHECK-LABEL: "sym_name" = "f"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()
