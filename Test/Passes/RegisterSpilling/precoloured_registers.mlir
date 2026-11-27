// RUN: veir-opt %s -p='register-spilling-riscv64' | filecheck %s

// A used precoloured value takes up one of the 27 registers, but is never evicted.
// Unused arguments are ignored

"builtin.module"() ({

  // Precoloured and used argument stays in its register, unused argument is ignored.
  "riscv_cf.func"() <{sym_name = "precoloured_argument", function_type = (!riscv.reg<x10>, !riscv.reg<x11>) -> ()}> ({
  ^entry(%a : !riscv.reg<x10>, %unused : !riscv.reg<x11>):
    %1 = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %2 = "riscv.li"() <{value = 2 : i64}> : () -> !riscv.reg
    %3 = "riscv.li"() <{value = 3 : i64}> : () -> !riscv.reg
    %4 = "riscv.li"() <{value = 4 : i64}> : () -> !riscv.reg
    %5 = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %6 = "riscv.li"() <{value = 6 : i64}> : () -> !riscv.reg
    %7 = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %8 = "riscv.li"() <{value = 8 : i64}> : () -> !riscv.reg
    %9 = "riscv.li"() <{value = 9 : i64}> : () -> !riscv.reg
    %10 = "riscv.li"() <{value = 10 : i64}> : () -> !riscv.reg
    %11 = "riscv.li"() <{value = 11 : i64}> : () -> !riscv.reg
    %12 = "riscv.li"() <{value = 12 : i64}> : () -> !riscv.reg
    %13 = "riscv.li"() <{value = 13 : i64}> : () -> !riscv.reg
    %14 = "riscv.li"() <{value = 14 : i64}> : () -> !riscv.reg
    %15 = "riscv.li"() <{value = 15 : i64}> : () -> !riscv.reg
    %16 = "riscv.li"() <{value = 16 : i64}> : () -> !riscv.reg
    %17 = "riscv.li"() <{value = 17 : i64}> : () -> !riscv.reg
    %18 = "riscv.li"() <{value = 18 : i64}> : () -> !riscv.reg
    %19 = "riscv.li"() <{value = 19 : i64}> : () -> !riscv.reg
    %20 = "riscv.li"() <{value = 20 : i64}> : () -> !riscv.reg
    %21 = "riscv.li"() <{value = 21 : i64}> : () -> !riscv.reg
    %22 = "riscv.li"() <{value = 22 : i64}> : () -> !riscv.reg
    %23 = "riscv.li"() <{value = 23 : i64}> : () -> !riscv.reg
    %24 = "riscv.li"() <{value = 24 : i64}> : () -> !riscv.reg
    %25 = "riscv.li"() <{value = 25 : i64}> : () -> !riscv.reg
    %26 = "riscv.li"() <{value = 26 : i64}> : () -> !riscv.reg
    %27 = "riscv.li"() <{value = 27 : i64}> : () -> !riscv.reg
    %s1 = "riscv.add"(%1, %a) : (!riscv.reg, !riscv.reg<x10>) -> !riscv.reg
    %s2 = "riscv.add"(%2, %3) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s4 = "riscv.add"(%4, %5) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s6 = "riscv.add"(%6, %7) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s8 = "riscv.add"(%8, %9) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s10 = "riscv.add"(%10, %11) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s12 = "riscv.add"(%12, %13) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s14 = "riscv.add"(%14, %15) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s16 = "riscv.add"(%16, %17) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s18 = "riscv.add"(%18, %19) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s20 = "riscv.add"(%20, %21) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s22 = "riscv.add"(%22, %23) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s24 = "riscv.add"(%24, %25) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s26 = "riscv.add"(%26, %27) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "precoloured_argument"
  // CHECK-NEXT:  ^{{[^ ]+}}([[A:%[^ ]+]] : !riscv.reg<x10>, %{{[^ ]+}} : !riscv.reg<x11>):
  // CHECK-NEXT:  [[V1:%[^ ]+]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V2:%[^ ]+]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V3:%[^ ]+]] = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V4:%[^ ]+]] = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V5:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V6:%[^ ]+]] = "riscv.li"() <{"value" = 6 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V7:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V8:%[^ ]+]] = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V9:%[^ ]+]] = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V10:%[^ ]+]] = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V11:%[^ ]+]] = "riscv.li"() <{"value" = 11 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V12:%[^ ]+]] = "riscv.li"() <{"value" = 12 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V13:%[^ ]+]] = "riscv.li"() <{"value" = 13 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V14:%[^ ]+]] = "riscv.li"() <{"value" = 14 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V15:%[^ ]+]] = "riscv.li"() <{"value" = 15 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V16:%[^ ]+]] = "riscv.li"() <{"value" = 16 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V17:%[^ ]+]] = "riscv.li"() <{"value" = 17 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V18:%[^ ]+]] = "riscv.li"() <{"value" = 18 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V19:%[^ ]+]] = "riscv.li"() <{"value" = 19 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V20:%[^ ]+]] = "riscv.li"() <{"value" = 20 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V21:%[^ ]+]] = "riscv.li"() <{"value" = 21 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V22:%[^ ]+]] = "riscv.li"() <{"value" = 22 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V23:%[^ ]+]] = "riscv.li"() <{"value" = 23 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V24:%[^ ]+]] = "riscv.li"() <{"value" = 24 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V25:%[^ ]+]] = "riscv.li"() <{"value" = 25 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[V26:%[^ ]+]] = "riscv.li"() <{"value" = 26 : i64}> : () -> !riscv.reg

  // Value 27 needs a register. The argument is not evicted, the oldest other value is.
  // CHECK-NEXT:  [[S1:%[^ ]+]] = "riscv_regalloc.spill"([[V1]]) : (!riscv.reg) -> !riscv.stack
  // CHECK-NEXT:  [[V27:%[^ ]+]] = "riscv.li"() <{"value" = 27 : i64}> : () -> !riscv.reg

  // Value 1 is reloaded, which evicts 2. The argument is still in its register.
  // CHECK-NEXT:  [[S2:%[^ ]+]] = "riscv_regalloc.spill"([[V2]]) : (!riscv.reg) -> !riscv.stack
  // CHECK-NEXT:  [[R1:%[^ ]+]] = "riscv_regalloc.reload"([[S1]]) : (!riscv.stack) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[R1]], [[A]]) : (!riscv.reg, !riscv.reg<x10>) -> !riscv.reg

  // Value 1 and the argument died at the add, so reloading 2 evicts nothing.
  // CHECK-NEXT:  [[R2:%[^ ]+]] = "riscv_regalloc.reload"([[S2]]) : (!riscv.stack) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[R2]], [[V3]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V4]], [[V5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V6]], [[V7]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V8]], [[V9]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V10]], [[V11]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V12]], [[V13]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V14]], [[V15]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V16]], [[V17]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V18]], [[V19]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V20]], [[V21]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V22]], [[V23]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V24]], [[V25]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[V26]], [[V27]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()
  // CHECK-NEXT:  }) : () -> ()

}) : () -> ()
