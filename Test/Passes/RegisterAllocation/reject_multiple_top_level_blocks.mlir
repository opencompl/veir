// RUN: not veir-opt %s --allow-unregistered-dialect -p=register-allocation-riscv64 2>&1 | filecheck %s

// The pass reads the functions out of the root's first block. A verified `builtin.module`
// body holds at most one, since its region is a graph region, but the graph-region rule
// exempts unregistered operations -- which is what the root may be.
"test.outer"() ({
^bb0:
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "cf.br"()[^bb1] : () -> ()
^bb1:
  "riscv_cf.func"() <{sym_name = "g", function_type = () -> ()}> ({
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "cf.br"()[^bb1] : () -> ()
}) : () -> ()

// CHECK: register allocation expects a module body with a single block
