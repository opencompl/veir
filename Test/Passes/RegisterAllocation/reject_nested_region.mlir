// RUN: not veir-opt %s --allow-unregistered-dialect -p=register-allocation-riscv64 2>&1 | filecheck %s

// The allocator only scans the ops of one block, so values defined in a nested region
// would silently keep their unallocated types.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    "test.container"() ({
      %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    }) : () -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation does not support operations with nested regions
