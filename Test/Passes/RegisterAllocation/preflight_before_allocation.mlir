// RUN: not veir-opt %s -p=register-allocation-riscv64 2>&1 | filecheck %s

// The later unsupported body must be rejected before allocation reaches the i32 value.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
  ^entry:
    "riscv_cf.branch"()[^next] : () -> ()
  ^next:
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation requires a single-block function
