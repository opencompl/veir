// RUN: not veir-opt %s --allow-unregistered-dialect -p=register-allocation-riscv64 2>&1 | filecheck %s

// The pass reads the functions out of the root's single region. A verified `builtin.module`
// always has exactly one, but the pipeline roots the pass at whatever operation it is given,
// and an unregistered operation makes no promise about its regions.
"test.outer"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}, {
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation expects a module with a single region
