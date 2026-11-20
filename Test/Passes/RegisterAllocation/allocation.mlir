// RUN: veir-opt %s --print-op-generic -p=register-allocation-riscv64 | filecheck %s

// The whole accepted shape in one module: a non-function sibling and function
// declarations are passed over, every function body is allocated, and virtual
// numbering restarts per function. Bodies cover a return-only block, concrete
// allocation with reuse, and a fixed x0 result left alone.
// Virtual j-register syntax is output-only; inputs must use unallocated types.
"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64,
    global_type = i32, linkage = #llvm.linkage<external>, sym_name = "global",
    value = 41 : i32}> ({}) : () -> ()

  "riscv_cf.func"() <{sym_name = "external_before", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()

  "riscv_cf.func"() <{sym_name = "return_only", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  "riscv_cf.func"() <{sym_name = "arithmetic", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %sum = "riscv.add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  "riscv_cf.func"() <{sym_name = "external_between", function_type = (!riscv.reg) -> !riscv.reg}> ({}) : () -> ()

  "riscv_cf.func"() <{sym_name = "fixed_zero", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %sum = "riscv.add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %zero = "rv64.get_register"() : () -> !riscv.reg<x0>
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "llvm.mlir.global"()
// CHECK-SAME:  "sym_name" = "global"
// CHECK-SAME:  "value" = 41 : i32
// CHECK-SAME:  }> ({}) : () -> ()

// A declaration keeps its unallocated argument and result types.
// CHECK-LABEL: "riscv_cf.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "external_before"}> ({}) : () -> ()

// CHECK-LABEL: "sym_name" = "return_only"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()

// Require every result and operand to be allocated, not merely one j-register.
// CHECK-LABEL: "sym_name" = "arithmetic"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  [[A:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
// CHECK-NEXT:  [[B:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg<j1>
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[A]], [[B]]) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()

// CHECK-LABEL: "riscv_cf.func"() <{"function_type" = (!riscv.reg) -> !riscv.reg, "sym_name" = "external_between"}> ({}) : () -> ()

// Numbering restarts at j0 for each function.
// CHECK-LABEL: "sym_name" = "fixed_zero"
// CHECK-NEXT:  ^{{[^ ]+}}():
// CHECK-NEXT:  [[ZA:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg<j0>
// CHECK-NEXT:  [[ZB:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg<j1>
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[ZA]], [[ZB]]) : (!riscv.reg<j0>, !riscv.reg<j1>) -> !riscv.reg<j0>
// CHECK-NEXT:  %{{[^ ]+}} = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT:  "riscv_cf.return"() : () -> ()
// CHECK-NEXT:  }) : () -> ()
