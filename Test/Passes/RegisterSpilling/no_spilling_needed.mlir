// RUN: veir-opt %s -p='register-spilling-riscv64' | filecheck %s 

// no spilling required
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "return_only", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "return_only"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()
  // CHECK-NEXT:  }) : () -> ()

  // less than 28 values
  "riscv_cf.func"() <{sym_name = "arithmetic", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %sum = "riscv.add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // Fewer live values than registers, so the function is left unchanged.
  // CHECK-LABEL: "sym_name" = "arithmetic"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  [[A:%[^ ]+]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  [[B:%[^ ]+]] = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"([[A]], [[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()
  // CHECK-NEXT:  }) : () -> ()

  // more than 28 values loaded, but not used -> no spilling
  "riscv_cf.func"() <{sym_name = "unused_values", function_type = () -> ()}> ({
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
    %28 = "riscv.li"() <{value = 28 : i64}> : () -> !riscv.reg
    %29 = "riscv.li"() <{value = 29 : i64}> : () -> !riscv.reg
    %30 = "riscv.li"() <{value = 30 : i64}> : () -> !riscv.reg
    %31 = "riscv.li"() <{value = 31 : i64}> : () -> !riscv.reg
    %32 = "riscv.li"() <{value = 32 : i64}> : () -> !riscv.reg
    %33 = "riscv.li"() <{value = 33 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

  // Values that are never used do not occupy a register, so nothing is spilled.
  // CHECK-LABEL: "sym_name" = "unused_values"
  // CHECK-NEXT:  ^{{[^ ]+}}():
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 6 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 11 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 12 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 13 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 14 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 15 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 16 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 17 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 18 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 19 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 20 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 21 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 22 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 23 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 24 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 25 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 26 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 27 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 28 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 29 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 30 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 31 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 32 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 33 : i64}> : () -> !riscv.reg
  // CHECK-NEXT:  "riscv_cf.return"() : () -> ()
  // CHECK-NEXT:  }) : () -> ()


}) : () -> ()



